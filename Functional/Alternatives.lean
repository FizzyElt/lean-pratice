structure NonEmptyList (α : Type) where
  head : α
  tail : List α
deriving Repr


instance : Append  (NonEmptyList α) where
  append xs ys := { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

structure RawInput where
  name : String
  birthYear : String

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
deriving Repr

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs


instance : Applicative (Validate ε) where
  pure := .ok
  seq f x := 
    match f with
      | .ok g => g <$> (x ())
      | .errors errs => 
        match x () with
          | .ok _ => .errors errs
          | .errors errs' => .errors (errs ++ errs')

def Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then 
    reportError "name" "Required"
  else
    pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β := 
  match val with
    | .errors errs => .errors errs
    | .ok x => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
    | none => reportError "birth year" "Must be digits"
    | some n => pure n

def checkBirthYear (thisYear year : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat


-- ---------------------------------------------

abbrev NonEmptyString := { s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr


def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α := 
  match a with
    | .ok x => .ok x
    | .errors errs1 =>
      match b () with
        | .ok x => .ok x
        | .errors errs2 => .errors (errs1 ++ errs2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput := 
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name 

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input
