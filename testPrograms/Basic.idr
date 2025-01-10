module Main

add : Int -> Int -> Int
add x y = x + y

main : IO ()
main = do
  putStrLn "Hello world"
  putStrLn "2 + 2 = \{show $ add 2 2}"
