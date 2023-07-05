structure RectanularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr


def volume (rec : RectanularPrism) : Float := 
  rec.height * rec.width * rec.depth


structure Point where
  x : Float
  y : Float
deriving Repr

structure Segment where
  a : Point
  b : Point
deriving Repr

def length (seg : Segment) : Float :=
  let { a, b } := seg
  Float.sqrt ((b.y - a.y)^2 + (b.x - a.x)^2)

