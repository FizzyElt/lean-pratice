def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

def ss : StateM Nat String := (fun a => toString a) <$> StateT.pure 1 

#eval (StateT.map (fun a => a ++ "fun") ss) 2



inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch l x r => 
    mapM f l >>= fun newl => 
    f x >>= fun hd => 
    mapM f r >>= fun newr =>
    pure (BinTree.branch newl hd newr)