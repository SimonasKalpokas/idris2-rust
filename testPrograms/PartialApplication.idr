module Main

apply : (a -> b) -> a -> b
apply fn x = fn x

add : Int -> Int -> Int
add x y = x + y

increment : Int -> Int
increment x = Main.apply add x 1

main : IO ()
main = do
  putStrLn "increment 1 = \{show $ Main.increment 1}"

  let add2 = Main.apply (flip add) 2
  putStrLn "2 + 2 = \{show $ add2 2}"

  let sum = foldl (\acc, cur => acc + cur) 0 [1..5]
  putStrLn "sum 1 through 5 = \{show sum}"
