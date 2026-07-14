param(
    [switch]$Strict
)

$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $PSScriptRoot
$paper = Join-Path $root 'paper'
$source = Join-Path $paper 'erdos1212_minimal_closure.tex'
$build = Join-Path $root 'build\paper'
$job = 'Li_Erdos_1212_Minimal_Closure_2026'
$pdf = Join-Path $paper "$job.pdf"

New-Item -ItemType Directory -Force -Path $build | Out-Null

foreach ($pass in 1..2) {
    & pdflatex `
        -interaction=nonstopmode `
        -halt-on-error `
        -file-line-error `
        "-jobname=$job" `
        "-output-directory=$build" `
        $source
    if ($LASTEXITCODE -ne 0) { throw "pdflatex failed on pass $pass" }
}

$builtPdf = Join-Path $build "$job.pdf"
$logFile = Join-Path $build "$job.log"
Copy-Item -LiteralPath $builtPdf -Destination $pdf -Force

if ($Strict) {
    $log = Get-Content -Raw -LiteralPath $logFile -Encoding UTF8
    $patterns = @(
        'Undefined control sequence',
        'LaTeX Warning: There were undefined references',
        'LaTeX Warning: Citation .* undefined',
        'Emergency stop',
        'Fatal error',
        'Overfull \\hbox',
        'Underfull \\hbox',
        'destination with the same identifier'
    )
    foreach ($pattern in $patterns) {
        if ($log -match $pattern) { throw "strict TeX gate failed: $pattern" }
    }

    $textFile = Join-Path $build "$job.txt"
    & pdftotext -layout $pdf $textFile
    if ($LASTEXITCODE -ne 0) { throw 'pdftotext failed' }
    $text = Get-Content -Raw -LiteralPath $textFile -Encoding UTF8
    foreach ($required in @(
        'The unchanged target',
        'Fixed-contour prime cancellation',
        'Certified translation kernel',
        'Twelve-prime directed interval certificate',
        'Theorem 6.1 (Closure of',
        '0.91717912709094451')) {
        if (-not $text.Contains($required)) {
            throw "strict manuscript gate failed: missing rendered text '$required'"
        }
    }
}

Write-Host "[paper:ok] paper/$job.pdf"
