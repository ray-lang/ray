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
    $arch = $env:PROCESSOR_ARCHITECTURE
    if (-not $arch) {
        $arch = ''
    }
    $arch = $arch.ToLowerInvariant()
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

function Ensure-UserPathContains {
    param(
        [Parameter(Mandatory = $true)]
        [string]$Entry
    )

    $userPath = [System.Environment]::GetEnvironmentVariable("Path", "User")
    $currentEntries = if ($userPath) {
        $userPath.Split(';') | Where-Object { $_ -ne '' }
    } else {
        @()
    }

    if ($currentEntries | Where-Object { $_.Trim().ToLowerInvariant() -eq $Entry.Trim().ToLowerInvariant() }) {
        return $false
    }

    $newPath = if ([string]::IsNullOrEmpty($userPath)) {
        $Entry
    } else {
        "$userPath;$Entry"
    }

    try {
        [System.Environment]::SetEnvironmentVariable("Path", $newPath, "User")
        return $true
    } catch {
        Write-Warning "Unable to modify user PATH automatically: $($_.Exception.Message)"
        return $false
    }
}

if ($env:OS -ne 'Windows_NT') {
    throw "error: install-ray.ps1 is intended for Windows hosts only"
}

if (-not $ReleaseTag) {
    $ReleaseTag = Resolve-LatestTag
}

$hostArch = Resolve-Architecture
$repoBase = "https://github.com/ray-lang/ray/releases/download/$ReleaseTag"
$cliAsset = "ray-cli-windows-$hostArch-$ReleaseTag.exe"

$tempDir = New-TempDirectory
try {
    $cliPath = Join-Path $tempDir $cliAsset

    Write-Host "==> downloading $cliAsset"
    Invoke-WebRequest -Uri "$repoBase/$cliAsset" -OutFile $cliPath -UseBasicParsing

    $rayRoot = if ($env:RAY_PATH) { $env:RAY_PATH } else { Join-Path $env:USERPROFILE '.ray' }
    $rayBinDir = Join-Path $rayRoot 'bin'
    $null = New-Item -ItemType Directory -Path $rayBinDir -Force
    $rayBin = Join-Path $rayBinDir 'ray.exe'

    Write-Host "==> installing CLI to $rayBin"
    Copy-Item -Path $cliPath -Destination $rayBin -Force
    Write-Host "==> bootstrapping toolchain via ray bootstrap $ReleaseTag"
    & $rayBin bootstrap $ReleaseTag

    $updatedPath = Ensure-UserPathContains -Entry $rayBinDir
    if ($updatedPath) {
        if (-not (($env:PATH -split ';') -contains $rayBinDir)) {
            $env:PATH = "$env:PATH;$rayBinDir"
        }
        Write-Host "==> added $rayBinDir to your PATH"
    } elseif ((($env:PATH -split ';') -contains $rayBinDir) -or (([System.Environment]::GetEnvironmentVariable("Path", "User") -split ';') -contains $rayBinDir)) {
        Write-Host "==> $rayBinDir already present in PATH"
    } else {
        Write-Warning "Add '$rayBinDir' to your PATH manually to use 'ray' globally."
    }

    Write-Host ""
    Write-Host "Ray installed!"
    Write-Host "- CLI:   $rayBin"
    Write-Host "- Root:  $rayRoot"
    $onPath = (($env:PATH -split ';') -contains $rayBinDir) -or (([System.Environment]::GetEnvironmentVariable("Path", "User") -split ';') -contains $rayBinDir) -or (([System.Environment]::GetEnvironmentVariable("Path", "Machine") -split ';') -contains $rayBinDir)
    if ($onPath) {
        Write-Host "- Bin:   $rayBinDir (on PATH)"
    } else {
        Write-Host "- Bin:   $rayBinDir (not yet on PATH)"
    }
} finally {
    if (Test-Path $tempDir) {
        Remove-Item -Path $tempDir -Recurse -Force
    }
}
