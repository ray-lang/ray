param(
    [Parameter(Position = 0)]
    [string]$ReleaseTag
)

$ErrorActionPreference = 'Stop'

function Resolve-LatestTag {
    Write-Host "==> detecting latest Ray release"
    $api = 'https://api.github.com/repos/ray-lang/ray/releases/latest'
    try {
        $response = Invoke-RestMethod -Uri $api -UseBasicParsing
    } catch {
        throw "error: unable to query GitHub for the latest release tag: $($_.Exception.Message)"
    }

    if (-not $response.tag_name) {
        throw "error: unable to determine latest release tag; supply one explicitly"
    }

    return $response.tag_name
}

function Resolve-Architecture {
    $arch = ($env:PROCESSOR_ARCHITECTURE ?? '') .ToLowerInvariant()
    switch ($arch) {
        'amd64' { return 'x86_64' }
        'x86_64' { return 'x86_64' }
        'arm64' { return 'arm64' }
        'aarch64' { return 'arm64' }
        default { throw "error: unsupported architecture '$arch'" }
    }
}

function New-TempDirectory {
    $root = [System.IO.Path]::GetTempPath()
    $dir = Join-Path $root ("ray-install-" + [System.Guid]::NewGuid().ToString("n"))
    return (New-Item -ItemType Directory -Path $dir -Force).FullName
}

function Expand-ToolchainArchive {
    param(
        [Parameter(Mandatory = $true)]
        [string]$ArchivePath,
        [Parameter(Mandatory = $true)]
        [string]$Destination,
        [Parameter(Mandatory = $true)]
        [string]$TempDir
    )

    $extension = [System.IO.Path]::GetExtension($ArchivePath)
    if ($extension -ieq '.zip') {
        Expand-Archive -Path $ArchivePath -DestinationPath $Destination -Force
        return
    }

    $tar = Get-Command tar -ErrorAction SilentlyContinue
    if (-not $tar) {
        throw "error: 'tar' is required to extract the toolchain archive"
    }

    $tarSupportsZstd = $false
    try {
        $helpOutput = & $tar.Source --help 2>&1
        if ($helpOutput -match '--zstd') {
            $tarSupportsZstd = $true
        }
    } catch {
        # ignore --help failure; assume no --zstd support
    }

    if ($tarSupportsZstd) {
        & $tar.Source --zstd -xf $ArchivePath -C $Destination
        return
    }

    $zstd = Get-Command zstd -ErrorAction SilentlyContinue
    if (-not $zstd) {
        throw "error: tar lacks --zstd support and 'zstd' is not installed; install zstd or provide a zip archive"
    }

    $decompressed = Join-Path $TempDir 'toolchain.tar'
    & $zstd.Source -d $ArchivePath -o $decompressed
    & $tar.Source -xf $decompressed -C $Destination
}

if (-not $IsWindows) {
    throw "error: install-ray.ps1 is intended for Windows hosts only"
}

if (-not $ReleaseTag) {
    $ReleaseTag = Resolve-LatestTag
}

$hostArch = Resolve-Architecture
$repoBase = "https://github.com/ray-lang/ray/releases/download/$ReleaseTag"
$cliAsset = "ray-cli-windows-$hostArch-$ReleaseTag.exe"
$toolchainAsset = "ray-toolchain-windows-$hostArch-$ReleaseTag.tar.zst"

$tempDir = New-TempDirectory
try {
    $cliPath = Join-Path $tempDir $cliAsset
    $toolchainPath = Join-Path $tempDir $toolchainAsset

    Write-Host "==> downloading $cliAsset"
    Invoke-WebRequest -Uri "$repoBase/$cliAsset" -OutFile $cliPath -UseBasicParsing

    Write-Host "==> downloading $toolchainAsset"
    Invoke-WebRequest -Uri "$repoBase/$toolchainAsset" -OutFile $toolchainPath -UseBasicParsing

    $rayRoot = if ($env:RAY_PATH) { $env:RAY_PATH } else { Join-Path $env:USERPROFILE '.ray' }
    $rayBinDir = Join-Path $rayRoot 'bin'
    $null = New-Item -ItemType Directory -Path $rayBinDir -Force
    $rayBin = Join-Path $rayBinDir 'ray.exe'

    Write-Host "==> installing CLI to $rayBin"
    Copy-Item -Path $cliPath -Destination $rayBin -Force

    Write-Host "==> extracting toolchain into $rayRoot"
    Expand-ToolchainArchive -ArchivePath $toolchainPath -Destination $rayRoot -TempDir $tempDir

    $installBinDir = if ($env:INSTALL_BIN) { $env:INSTALL_BIN } else { Join-Path $env:USERPROFILE '.local\bin' }
    $null = New-Item -ItemType Directory -Path $installBinDir -Force
    $cliTarget = Join-Path $installBinDir 'ray.exe'

    $symlinked = $false
    try {
        if (Test-Path $cliTarget) {
            Remove-Item -Path $cliTarget -Force
        }
        New-Item -ItemType SymbolicLink -Path $cliTarget -Target $rayBin -Force | Out-Null
        $symlinked = $true
        Write-Host "==> symlinked CLI to $cliTarget"
    } catch {
        Write-Warning "unable to create symlink at $cliTarget; copying CLI instead"
        Copy-Item -Path $rayBin -Destination $cliTarget -Force
    }

    Write-Host ""
    Write-Host "Ray installed!"
    Write-Host "- CLI:   $rayBin"
    Write-Host "- Root:  $rayRoot"
    if (-not $symlinked) {
        Write-Host "- Bin:   $cliTarget"
    }

    $pathEntries = ($env:PATH -split ';') | Where-Object { $_ -ne '' }
    if ($pathEntries -notcontains $installBinDir) {
        Write-Warning "Add '$installBinDir' to your PATH to use 'ray' globally."
    }
} finally {
    if (Test-Path $tempDir) {
        Remove-Item -Path $tempDir -Recurse -Force
    }
}
