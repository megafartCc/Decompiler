param(
    [Parameter(Mandatory = $true)]
    [string]$SourceRoot,

    [Parameter(Mandatory = $true)]
    [string]$OutputRoot,

    [string]$DecompilerExe = "",

    [switch]$Resume,

    [int]$Jobs = 1,

    [switch]$VerboseDecompiler,

    [switch]$StrictStructured,

    [switch]$AllowRawFallback
)

$ErrorActionPreference = "Stop"

if ([string]::IsNullOrWhiteSpace($DecompilerExe)) {
    $candidates = @(
        (Join-Path $PSScriptRoot "luau_decompiler.exe"),
        (Join-Path $PSScriptRoot "..\\luau_decompiler.exe"),
        "luau_decompiler.exe"
    )

    foreach ($candidate in $candidates) {
        if (Test-Path -LiteralPath $candidate) {
            $DecompilerExe = $candidate
            break
        }
    }
}

if (-not (Test-Path -LiteralPath $DecompilerExe)) {
    throw "Decompiler executable not found: $DecompilerExe (pass -DecompilerExe <path>)"
}

if (-not (Test-Path -LiteralPath $SourceRoot)) {
    throw "Source root not found: $SourceRoot"
}

$resolvedSourceRoot = (Resolve-Path -LiteralPath $SourceRoot).Path.TrimEnd('\')

if ((Test-Path -LiteralPath $OutputRoot) -and -not $Resume) {
    Remove-Item -LiteralPath $OutputRoot -Recurse -Force
}
if (-not (Test-Path -LiteralPath $OutputRoot)) {
    New-Item -ItemType Directory -Path $OutputRoot | Out-Null
}

$luacFiles = Get-ChildItem -LiteralPath $resolvedSourceRoot -Recurse -File -Filter *.luac | Sort-Object FullName
$otherFiles = Get-ChildItem -LiteralPath $resolvedSourceRoot -Recurse -File | Where-Object { $_.Extension -ne '.luac' } | Sort-Object FullName

$errors = @()
$copyWarnings = @()
$results = @()
$index = 0
$reservedOutputPaths = New-Object 'System.Collections.Generic.HashSet[string]' ([System.StringComparer]::OrdinalIgnoreCase)
foreach ($bytecodeFile in $luacFiles) {
    $relativePath = $bytecodeFile.FullName.Substring($resolvedSourceRoot.Length).TrimStart('\')
    $outputRelativePath = [System.IO.Path]::ChangeExtension($relativePath, '.lua')
    $reservedPath = Join-Path $OutputRoot $outputRelativePath
    [void]$reservedOutputPaths.Add($reservedPath)
}

function Invoke-Decompile {
    param(
        [string[]]$Arguments
    )
    $prevErrorAction = $ErrorActionPreference
    try {
        $ErrorActionPreference = "Continue"
        if ($VerboseDecompiler) {
            & $DecompilerExe @Arguments
        } else {
            & $DecompilerExe @Arguments > $null 2> $null
        }
        return $LASTEXITCODE
    } finally {
        $ErrorActionPreference = $prevErrorAction
    }
}

if ($Jobs -lt 1) {
    $Jobs = 1
}

if ($Jobs -le 1 -or $luacFiles.Count -le 1) {
    foreach ($file in $luacFiles) {
        $index++
        if (-not (Test-Path -LiteralPath $file.FullName)) {
            $errors += [pscustomobject]@{
                File = $file.FullName
                ExitCode = -9001
                Stage = "decompile"
                Message = "Source bytecode file disappeared before processing"
            }
            continue
        }
        $relativePath = $file.FullName.Substring($resolvedSourceRoot.Length).TrimStart('\')
        $outputRelativePath = [System.IO.Path]::ChangeExtension($relativePath, '.lua')
        $outputPath = Join-Path $OutputRoot $outputRelativePath
        $rawFallbackPath = [System.IO.Path]::ChangeExtension($outputPath, '.raw.txt')
        $outputDir = Split-Path -Parent $outputPath

        if (-not (Test-Path -LiteralPath $outputDir)) {
            New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
        }

        if ($Resume -and ((Test-Path -LiteralPath $outputPath) -or ($AllowRawFallback -and (Test-Path -LiteralPath $rawFallbackPath)))) {
            continue
        }

        $mode = "default"
        $defaultArgs = @($file.FullName, $outputPath)
        if ($StrictStructured) {
            $defaultArgs = @("--strict-structured", $file.FullName, $outputPath)
        }
        $exitCode = Invoke-Decompile $defaultArgs
        if ($exitCode -ne 0 -and $AllowRawFallback) {
            $mode = "raw"
            $exitCode = Invoke-Decompile @("--raw", $file.FullName, $rawFallbackPath)
        }

        if ($exitCode -ne 0) {
            $errors += [pscustomobject]@{
                File = $file.FullName
                ExitCode = $exitCode
            }
        } else {
            $results += [pscustomobject]@{
                File = $file.FullName
                Mode = $mode
            }
        }

        if (($index % 100) -eq 0) {
            Write-Host "[progress] Decompiled $index / $($luacFiles.Count)"
        }
    }
} else {
    $workerCount = [Math]::Min($Jobs, $luacFiles.Count)
    Write-Host "[parallel] Using $workerCount workers"

    $batches = @()
    for ($w = 0; $w -lt $workerCount; $w++) {
        $batches += ,(New-Object System.Collections.Generic.List[string])
    }

    for ($i = 0; $i -lt $luacFiles.Count; $i++) {
        $batches[$i % $workerCount].Add($luacFiles[$i].FullName)
    }

    $jobList = @()
    for ($w = 0; $w -lt $workerCount; $w++) {
        $batch = $batches[$w].ToArray()
        $jobArgs = @()
        $jobArgs += ,$batch
        $jobArgs += $resolvedSourceRoot
        $jobArgs += $OutputRoot
        $jobArgs += $DecompilerExe
        $jobArgs += [bool]$Resume
        $jobArgs += [bool]$VerboseDecompiler
        $jobArgs += [bool]$StrictStructured
        $jobArgs += [bool]$AllowRawFallback

        $jobList += Start-Job -ScriptBlock {
            param(
                [string[]]$Batch,
                [string]$ResolvedSourceRoot,
                [string]$OutputRootParam,
                [string]$DecompilerExeParam,
                [bool]$ResumeParam,
                [bool]$VerboseDecompilerParam,
                [bool]$StrictStructuredParam,
                [bool]$AllowRawFallbackParam
            )

            function Invoke-DecompileInJob {
                param([string[]]$Arguments)
                $prevErrorAction = $ErrorActionPreference
                try {
                    $ErrorActionPreference = "Continue"
                    if ($VerboseDecompilerParam) {
                        & $DecompilerExeParam @Arguments
                    } else {
                        & $DecompilerExeParam @Arguments > $null 2> $null
                    }
                    return $LASTEXITCODE
                } finally {
                    $ErrorActionPreference = $prevErrorAction
                }
            }

            $localResults = @()
            $localErrors = @()
            $processed = 0

            foreach ($filePath in $Batch) {
                $processed++
                if (-not (Test-Path -LiteralPath $filePath)) {
                    $localErrors += [pscustomobject]@{
                        File = $filePath
                        ExitCode = -9001
                        Stage = "decompile"
                        Message = "Source bytecode file disappeared before processing"
                    }
                    continue
                }
                $relativePath = $filePath.Substring($ResolvedSourceRoot.Length).TrimStart('\')
                $outputRelativePath = [System.IO.Path]::ChangeExtension($relativePath, '.lua')
                $outputPath = Join-Path $OutputRootParam $outputRelativePath
                $rawFallbackPath = [System.IO.Path]::ChangeExtension($outputPath, '.raw.txt')
                $outputDir = Split-Path -Parent $outputPath

                if (-not (Test-Path -LiteralPath $outputDir)) {
                    New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
                }

                if ($ResumeParam -and ((Test-Path -LiteralPath $outputPath) -or ($AllowRawFallbackParam -and (Test-Path -LiteralPath $rawFallbackPath)))) {
                    continue
                }

                $mode = "default"
                $defaultArgs = @($filePath, $outputPath)
                if ($StrictStructuredParam) {
                    $defaultArgs = @("--strict-structured", $filePath, $outputPath)
                }
                $exitCode = Invoke-DecompileInJob $defaultArgs
                if ($exitCode -ne 0 -and $AllowRawFallbackParam) {
                    $mode = "raw"
                    $exitCode = Invoke-DecompileInJob @("--raw", $filePath, $rawFallbackPath)
                }

                if ($exitCode -ne 0) {
                    $localErrors += [pscustomobject]@{
                        File = $filePath
                        ExitCode = $exitCode
                    }
                } else {
                    $localResults += [pscustomobject]@{
                        File = $filePath
                        Mode = $mode
                    }
                }
            }

            [pscustomobject]@{
                Results = $localResults
                Errors = $localErrors
                Processed = $processed
            }
        } -ArgumentList $jobArgs
    }

    $completed = 0
    while ($jobList.Count -gt 0) {
        $done = Wait-Job -Job $jobList -Any
        $payload = Receive-Job -Job $done
        Remove-Job -Job $done
        $jobList = $jobList | Where-Object { $_.Id -ne $done.Id }

        if ($null -ne $payload) {
            foreach ($entry in @($payload)) {
                if ($entry.Results) { $results += $entry.Results }
                if ($entry.Errors) { $errors += $entry.Errors }
                if ($null -ne $entry.Processed) {
                    $processedCount = ($entry.Processed | Measure-Object -Sum).Sum
                    $completed += [int]$processedCount
                }
            }
        }

        if (($completed % 100) -eq 0 -or $jobList.Count -eq 0) {
            Write-Host "[progress] Decompiled $completed / $($luacFiles.Count)"
        }
    }
}

foreach ($file in $otherFiles) {
    if (-not (Test-Path -LiteralPath $file.FullName)) {
        $copyWarnings += [pscustomobject]@{
            File = $file.FullName
            Code = -9002
            Stage = "copy"
            Message = "Source non-bytecode file disappeared before copy"
        }
        continue
    }
    $relativePath = $file.FullName.Substring($resolvedSourceRoot.Length).TrimStart('\')
    $outputPath = Join-Path $OutputRoot $relativePath
    if ($reservedOutputPaths.Contains($outputPath)) {
        $copyWarnings += [pscustomobject]@{
            File = $file.FullName
            Code = -9004
            Stage = "copy"
            Message = "Skipped copy to avoid overwriting decompiled output"
        }
        continue
    }
    $outputDir = Split-Path -Parent $outputPath

    if (-not (Test-Path -LiteralPath $outputDir)) {
        New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
    }

    try {
        Copy-Item -LiteralPath $file.FullName -Destination $outputPath -Force
    } catch {
        $copyWarnings += [pscustomobject]@{
            File = $file.FullName
            Code = -9003
            Stage = "copy"
            Message = $_.Exception.Message
        }
    }
}

$resultsJson = if ($results.Count -gt 0) { $results | ConvertTo-Json -Depth 3 } else { "[]" }
$errorsJson = if ($errors.Count -gt 0) { $errors | ConvertTo-Json -Depth 3 } else { "[]" }
$copyWarningsJson = if ($copyWarnings.Count -gt 0) { $copyWarnings | ConvertTo-Json -Depth 3 } else { "[]" }
$resultsJson | Set-Content -Path (Join-Path $OutputRoot "_decompile_results.json")
$errorsJson | Set-Content -Path (Join-Path $OutputRoot "_decompile_errors.json")
$copyWarningsJson | Set-Content -Path (Join-Path $OutputRoot "_copy_warnings.json")

Write-Host "[done] Decompiled $($luacFiles.Count - $errors.Count) of $($luacFiles.Count) bytecode files"
Write-Host "[done] Copied $($otherFiles.Count) non-bytecode files"
if ($copyWarnings.Count -gt 0) {
    Write-Host "[warn] Non-bytecode copy warnings: $($copyWarnings.Count)"
}

if ($errors.Count -gt 0) {
    $errors | ConvertTo-Json -Depth 3
    exit 1
}
