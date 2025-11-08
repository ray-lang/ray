param(
    [Parameter(Mandatory = $true)]
    [ValidateSet('x64', 'arm64')]
    [string]$Arch
)

choco install llvm --version=17.0.6 --allow-downgrade -y

$installDir = 'C:\Program Files\LLVM'
$prefix = "C:\llvm-$Arch"

if (Test-Path $prefix) {
    Remove-Item -Recurse -Force $prefix
}
Copy-Item -Recurse -Force $installDir $prefix

Write-Output "Using LLVM prefix: $prefix"

$binPath = Join-Path $prefix 'bin'
Add-Content -Path $env:GITHUB_PATH -Value $binPath
Add-Content -Path $env:GITHUB_ENV -Value "LLVM_SYS_170_PREFIX=$prefix"
Add-Content -Path $env:GITHUB_ENV -Value "LLVM_SYS_CONFIG_PATH=$($binPath)\llvm-config.exe"

& "$binPath\llvm-config.exe" --version
