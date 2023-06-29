import Std

open Std.HashMap

structure Environment where 
  path : String
  home : String
  user : String
  deriving Repr

def getEnvDefault (name : String) : IO String := do
  let val? ← IO.getEnv name
  return match val? with
          | none => ""
          | some s => s


def loadEnv : IO Environment := do
  let path ← getEnvDefault "PATH"
  let home ← getEnvDefault "HOME"
  let user ← getEnvDefault "USER"
  return { path, home ,user }


def readerFunc1 : ReaderM Environment Float := do
  let env ← read
  let l1 := env.path.length
  let l2 := env.home.length * 2
  let l3 := env.user.length * 3
  return (l1 + l2 + l3).toFloat * 2.1

def readerFunc2 : ReaderM Environment Nat := 
  readerFunc1 >>= (fun x => return 2 + (x.floor.toUInt32.toNat))

def readerFunc3 : ReaderM Environment String := do
  let x ← readerFunc2
  return "Result: " ++ toString x

def main : IO Unit := do 
  let env ← loadEnv
  let str := readerFunc3.run env
  IO.println str

#eval main


