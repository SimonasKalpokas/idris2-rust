module Main

StringOrInt : Bool -> Type
StringOrInt True = Int
StringOrInt False = String

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt True = 94
getStringOrInt False = "Ninety four"

showType : Type -> String
showType Int = "Int"
showType String = "String"
showType _ = "Not String or Int"

main : IO ()
main = do
  let strVal = getStringOrInt False
  let intVal = getStringOrInt True
  putStrLn $ (show intVal) ++ " = " ++ strVal

  let strType = StringOrInt False
  let intType = StringOrInt True

  putStrLn $ "String type: " ++ (showType strType)
  putStrLn $ "Int type: " ++ (showType intType)


