structure Config where
  useASCII : Bool := false
  showDotFile : Bool := false
  currentPrefix : String := ""

structure TotalInfo where
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


abbrev TotalInfoIO (α : Type) : Type := StateT TotalInfo IO α


def TotalInfoIO.run (action : TotalInfoIO α) (cfg : TotalInfo) : IO α :=
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

def showFileName (cfg : Config) (file : String) : TotalInfoIO Unit := 
  IO.println s!"{cfg.currentPrefix} {file}"

def showDirName (cfg : Config) (dir : String) : TotalInfoIO Unit := 
  IO.println s!"{cfg.currentPrefix} {dir}/"

def showTotal : TotalInfoIO Unit := do
  IO.println s!"{(← get).file} files in {(← get).dir} directories"

partial def dirTree (path : System.FilePath) (cfg : Config) : TotalInfoIO Unit := do
  match ← toEntry path with
    | none => pure ()
    | some (.file name) => 
      if !cfg.showDotFile && name.startsWith "." then 
        pure () 
      else 
        modify fun total => {total with file := total.file + 1}
        showFileName cfg name
    | some (.dir name) =>
      showDirName cfg name
      let contents ← path.readDir
      modify fun total => {total with dir := total.dir + 1}
      (doList contents.toList fun d =>
          dirTree d.path cfg.inDirectory)





def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      ((dirTree (← IO.currentDir) config) >>= fun _ => showTotal).run (TotalInfo.mk 0 0)
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) \n"
      IO.eprintln usage
      pure 1

