module Chapter5
  
import Data.Vect


readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do
  x <- getLine
  xs <- readVectLen k
  pure (x :: xs)

data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) =
  putStrLn $ show xs ++ " (length " ++ (show len) ++ ")"

readVect : IO (VectUnknown String)
readVect = do
  x <- getLine
  if (x == "")
  then pure (MkVect _ [])
  else do
    MkVect _ xs <- readVect
    pure (MkVect _ (x :: xs))

readVect' : IO (len ** Vect len String)
readVect' = do
  x <- getLine
  if (x == "")
  then pure (_ ** [])
  else do
    (_ ** xs) <- readVect'
    pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter First Vector: "
  (len1 ** vec1) <- readVect'
  putStrLn "Enter Second Vector: "
  (len2 ** vec2) <- readVect'
  case exactLength len1 vec2 of
        Nothing => putStrLn "Vectors are of different length"
        Just vec2'  => printLn (zip vec1 vec2')

readToBlank : IO (List String)
readToBlank = do
  x <- getLine
  if (x == "")
  then pure []
  else do
    xs <- readToBlank
    pure (x :: xs)

readAndSave : IO ()
readAndSave = do
  xs <- concat <$> readToBlank
  filename <- getLine
  _ <- writeFile filename xs
  pure ()

fileContents : (h : File) -> IO (n ** Vect n String)
fileContents h = do
  Right x <- fGetLine h
    | Left err => pure (_ ** [])
  (_ ** xs) <- fileContents h
  pure (_ ** x :: xs)

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right file <- openFile filename Read
    | Left err => pure (_ ** [])
  fileContents file
  

