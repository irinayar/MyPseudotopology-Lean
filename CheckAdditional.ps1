$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    & lake env lean @args
    $leanExitCode = $LASTEXITCODE
} finally {
    Pop-Location
}
exit $leanExitCode
