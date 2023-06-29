def List.last? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: [] => some x
  | _ :: xs => last? xs


#eval ([] : List Int).last?
#eval [1,2,3,4].last?


def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := match xs with
  | [] => none
  | x :: xss => if predicate x then some x else findFirst? xss predicate

#eval ([] : List Int).findFirst? (fun x => x == 1)
#eval ([2, 3, 1] : List Int).findFirst? (fun x => x == 1)


def Prod.swap {α β : Type} (pair : α × β) : β × α := (pair.snd, pair.fst)



def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := 
  match xs, ys with 
  | x :: xss, y :: yss => (x, y) :: zip xss yss
  | _, _ => []


def take {α : Type} (n : Int) (xs : List α) : (List α) :=
  match xs, n with
  | _, 0 => []
  | [],_ => []
  | x :: xss, n => x :: take (n - 1) xss

#eval take 1 [1, 2, 3]
#eval take 5 [1, 2, 3]

def distri {α β γ : Type} (x : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match x with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

def mul_to_sum {α : Type} (x : Bool × α) : α ⊕ α :=
  match x with
  | (true, a) => Sum.inl a
  | (false, a) => Sum.inr a