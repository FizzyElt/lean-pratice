structure Config where
  useASCII : Bool := false
  showDotFile : Bool := false
  currentPrefix : String := ""
  file : Nat := 0
  dir : Nat := 0

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}


abbrev ConfigIO (α : Type) : Type := StateT Config IO α


def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
 (fun v => v.fst) <$> (action cfg) 


def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
  
def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["-a"] => some {showDotFile := true}
  | ["--ascii"] => some {useASCII := true}
  | ["--ascii", "-a"] | ["-a", "--ascii"] => some {useASCII := true,  showDotFile := true}
  | _ => none


def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action


inductive Entry where
  | file : String → Entry
  | dir : String → Entry


def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))

def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← get).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← get).currentPrefix} {dir}/"

def showTotal : ConfigIO Unit := do
  IO.println s!"{(← get).file} files in {(← get).dir} directories"

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
    | none => pure ()
    | some (.file name) => 
      if !(← get).showDotFile && name.startsWith "." then 
        pure () 
      else 
        modify fun cfg => {cfg with file := cfg.file + 1}
        showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← path.readDir
      modify fun cfg => {cfg with dir := cfg.dir + 1}
      (doList contents.toList fun d =>
          dirTree d.path)





def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      (dirTree (← IO.currentDir) >>= fun _ => showTotal).run config
      
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) \n"
      IO.eprintln usage
      pure 1

