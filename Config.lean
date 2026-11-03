import Lean.Data.Json

/-!
# Paths of the files outside the repository

The paths are read from a JSON file (template: `smbrta-tmpl.json`). It is found as
`--config FILE`, else the environment variable `SMBRTA_CONFIG`, else the first `smbrta.json`
in the current directory or one of its parents. Relative paths in it are relative to the
directory of the config file.
-/

namespace Smbrta

structure Config where
  /-- the config file -/
  file : System.FilePath
  json : Lean.Json

def configName : String := "smbrta.json"

/-- the first `smbrta.json` in `d` or one of its parents -/
partial def findUp (d : System.FilePath) : IO (Option System.FilePath) := do
  let f := d / configName
  if ← f.pathExists then return some f
  match d.parent with
  | some p => if p == d then return none else findUp p
  | none => return none

def Config.load (explicit : Option String) : IO Config := do
  let file ← match explicit with
    | some f => pure (System.FilePath.mk f)
    | none => match ← IO.getEnv "SMBRTA_CONFIG" with
      | some f => pure (System.FilePath.mk f)
      | none => match ← findUp (← IO.currentDir) with
        | some f => pure f
        | none => throw (IO.userError s!"no {configName} found (copy smbrta-tmpl.json to a parent directory)")
  match Lean.Json.parse (← IO.FS.readFile file) with
  | .ok json => return { file, json }
  | .error e => throw (IO.userError s!"{file}: {e}")

/-- the path stored under `key`, resolved against the directory of the config file -/
def Config.path (c : Config) (key : String) : IO String := do
  match c.json.getObjValAs? String key with
  | .ok p =>
    let p := System.FilePath.mk p
    if p.isAbsolute then return p.toString
    else
      let dir := (← IO.FS.realPath (c.file.parent.getD ".")).toString
      return (System.FilePath.mk dir / p).toString
  | .error _ => throw (IO.userError s!"{c.file}: key \"{key}\" missing")

end Smbrta
