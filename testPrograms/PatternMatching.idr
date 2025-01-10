module Main

import Data.Vect

data Shape : Type where
  Circle : Double -> Shape
  Rectangle : Double -> Double -> Shape

area : Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h

index : Fin n -> Vect n a -> a
index FZ (x :: xs) = x
index (FS k) (_ :: xs) = Main.index k xs

main : IO ()
main = do
  let c = Circle 5.0
  let r = Rectangle 3.0 4.0
  putStrLn $ "Circle area: " ++ show (area c)
  putStrLn $ "Rectangle area: " ++ show (area r)

  let v = Main.index {a=Int} {n=3} 1 (2 :: 4 :: 5 :: Nil)

  putStrLn $ "Second element of vector: " ++ show v
