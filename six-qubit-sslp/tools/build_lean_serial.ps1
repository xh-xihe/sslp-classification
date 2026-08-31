param(
  [Parameter(Mandatory = $true, Position = 0)]
  [string[]] $Module
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$oleanRoot = Join-Path $repoRoot '.lake\build\lib\lean'
$stampRoot = Join-Path $repoRoot '.lake\build\serial-safe'

function Get-SourcePath([string] $ModuleName) {
  $relative = $ModuleName.Replace('.', [IO.Path]::DirectorySeparatorChar) + '.lean'
  return Join-Path $repoRoot $relative
}

function Get-OleanPath([string] $ModuleName) {
  $relative = $ModuleName.Replace('.', [IO.Path]::DirectorySeparatorChar) + '.olean'
  return Join-Path $oleanRoot $relative
}

function Get-IleanPath([string] $ModuleName) {
  $relative = $ModuleName.Replace('.', [IO.Path]::DirectorySeparatorChar) + '.ilean'
  return Join-Path $oleanRoot $relative
}

function Get-CPath([string] $ModuleName) {
  $relative = $ModuleName.Replace('.', [IO.Path]::DirectorySeparatorChar) + '.c'
  return Join-Path (Join-Path $repoRoot '.lake\build\ir') $relative
}

function Get-StampPath([string] $ModuleName) {
  $relative = $ModuleName.Replace('.', [IO.Path]::DirectorySeparatorChar) + '.sha256'
  return Join-Path $stampRoot $relative
}

function Test-SuccessStamp([string] $ModuleName, [string] $SourcePath) {
  $stamp = Get-StampPath $ModuleName
  if (-not (Test-Path -LiteralPath $stamp)) {
    return $false
  }
  $recorded = (Get-Content -LiteralPath $stamp -Raw).Trim()
  $current = (Get-FileHash -LiteralPath $SourcePath -Algorithm SHA256).Hash
  return $recorded -eq $current
}

function Get-LocalImports([string] $SourcePath) {
  $imports = [System.Collections.Generic.List[string]]::new()
  foreach ($line in Get-Content -LiteralPath $SourcePath) {
    $code = ($line -split '--', 2)[0].Trim()
    if ($code -notmatch '^import\s+(.+)$') {
      continue
    }
    foreach ($name in ($Matches[1] -split '\s+')) {
      if ($name -and (Test-Path -LiteralPath (Get-SourcePath $name))) {
        $imports.Add($name)
      }
    }
  }
  return $imports
}

function Get-UnreadyDependencies([string] $TargetModule) {
  $seen = [System.Collections.Generic.HashSet[string]]::new()
  $unready = [System.Collections.Generic.List[string]]::new()

  function Visit([string] $ModuleName, [bool] $IsTarget) {
    if (-not $seen.Add($ModuleName)) {
      return
    }

    $source = Get-SourcePath $ModuleName
    if (-not (Test-Path -LiteralPath $source)) {
      return
    }

    foreach ($dependency in Get-LocalImports $source) {
      Visit $dependency $false
    }

    if ($IsTarget) {
      return
    }

    $olean = Get-OleanPath $ModuleName
    if (-not (Test-Path -LiteralPath $olean)) {
      $unready.Add("$ModuleName (missing .olean)")
      return
    }
    $stamp = Get-StampPath $ModuleName
    if ((Test-Path -LiteralPath $stamp) -and
        -not (Test-SuccessStamp $ModuleName $source)) {
      $unready.Add("$ModuleName (source differs from its successful-build stamp)")
      return
    }
    if ((Get-Item -LiteralPath $olean).LastWriteTimeUtc -lt
        (Get-Item -LiteralPath $source).LastWriteTimeUtc) {
      $unready.Add("$ModuleName (stale .olean)")
      return
    }
    foreach ($dependency in Get-LocalImports $source) {
      $dependencyOlean = Get-OleanPath $dependency
      if ((Test-Path -LiteralPath $dependencyOlean) -and
          (Get-Item -LiteralPath $olean).LastWriteTimeUtc -lt
          (Get-Item -LiteralPath $dependencyOlean).LastWriteTimeUtc) {
        $unready.Add("$ModuleName (.olean predates imported $dependency)")
        return
      }
    }
  }

  Visit $TargetModule $true
  return $unready
}

Push-Location $repoRoot
try {
  foreach ($target in $Module) {
    $source = Get-SourcePath $target
    if (-not (Test-Path -LiteralPath $source)) {
      throw "No local Lean source found for module $target"
    }

    $running = Get-Process -Name lean,lake -ErrorAction SilentlyContinue
    if ($running) {
      $summary = ($running | ForEach-Object { "$($_.ProcessName):$($_.Id)" }) -join ', '
      throw "Refusing to build while Lean/Lake is already running: $summary"
    }

    $unready = @(Get-UnreadyDependencies $target)
    if ($unready.Count -ne 0) {
      Write-Error ("Refusing to build $target because its local import closure is not prebuilt:`n  " +
        ($unready -join "`n  "))
    }

    Write-Output "BEGIN $target"
    # Compile exactly one source file.  `lake build` is intentionally avoided:
    # when several imported modules become stale, Lake may elaborate them in
    # parallel and multiply Lean's multi-gigabyte working set.  The checks above
    # require the whole local import closure to be ready first, so a direct
    # one-threaded Lean invocation is sufficient and resource-predictable.
    $olean = Get-OleanPath $target
    $ilean = Get-IleanPath $target
    $cFile = Get-CPath $target
    foreach ($output in @($olean, $ilean, $cFile)) {
      New-Item -ItemType Directory -Path (Split-Path -Parent $output) -Force | Out-Null
    }
    & lake env lean -j 1 -E warning $source -o $olean -i $ilean -c $cFile --json
    if ($LASTEXITCODE -ne 0) {
      exit $LASTEXITCODE
    }
    $stamp = Get-StampPath $target
    $stampDirectory = Split-Path -Parent $stamp
    New-Item -ItemType Directory -Path $stampDirectory -Force | Out-Null
    $hash = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash
    Set-Content -LiteralPath $stamp -Value $hash -NoNewline
    Write-Output "DONE  $target"
  }
}
finally {
  Pop-Location
}
