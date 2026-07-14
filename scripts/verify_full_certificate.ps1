param(
    [Parameter(Mandatory = $true)]
    [string]$Payload
)

$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
$payloadPath = (Resolve-Path -LiteralPath $Payload).Path

python (Join-Path $PSScriptRoot 'verify_publication.py') --payload $payloadPath
if ($LASTEXITCODE -ne 0) { throw 'payload hash verification failed' }

$build = Join-Path $root 'build'
New-Item -ItemType Directory -Force -Path $build | Out-Null
$checker = Join-Path $build 'repeat_interval_check.exe'

if (-not (Get-Command cl.exe -ErrorAction SilentlyContinue)) {
    $vswhere = "${env:ProgramFiles(x86)}\Microsoft Visual Studio\Installer\vswhere.exe"
    if (-not (Test-Path -LiteralPath $vswhere)) {
        throw 'MSVC compiler not found and vswhere.exe is unavailable'
    }
    $install = & $vswhere -latest -products * `
        -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 `
        -property installationPath
    if (-not $install) { throw 'Visual Studio C++ Build Tools not found' }
    $vcvars = Join-Path $install 'VC\Auxiliary\Build\vcvars64.bat'
    if (-not (Test-Path -LiteralPath $vcvars)) { throw "missing $vcvars" }
    $environment = & cmd.exe /s /c "`"$vcvars`" >nul && set"
    foreach ($line in $environment) {
        if ($line -match '^([^=]+)=(.*)$') {
            Set-Item -Path "Env:$($matches[1])" -Value $matches[2]
        }
    }
}

nvcc -O3 -std=c++17 (Join-Path $root 'kernel\repeat_interval_check.cu') -o $checker
if ($LASTEXITCODE -ne 0) { throw 'nvcc failed' }

& $checker `
    (Join-Path $payloadPath 'repeat_phase_witness_u_c1e-4.bin') `
    (Join-Path $payloadPath 'repeat_phase_cert_s0_double.bin') `
    (Join-Path $payloadPath 'repeat_phase_cert_s1_double.bin') `
    (Join-Path $payloadPath 'repeat_scalar_upper_s0_0_40_u.bin') `
    (Join-Path $payloadPath 'repeat_scalar_upper_s1_0_24_u.bin') `
    (Join-Path $payloadPath 'repeat_scalar_upper_fresh_25_400_u.bin') `
    (Join-Path $payloadPath 'repeat_scalar_upper_unit_41_400_u.bin')
if ($LASTEXITCODE -ne 0) { throw 'directed interval certificate failed' }

Write-Host '[certificate:ok] full dense replay passed'
