module Main

import Data.Vect

------------------------
--- replWith example ---
------------------------

sumInputs : Integer -> String -> Maybe (String, Integer)
sumInputs tot inp =
  let val = cast inp
  in if val < 0
     then Nothing
     else let newVal = tot + val
          in Just ("Subtotal: " ++ show newVal ++ "\n", newVal)

main' : IO ()
main' = replWith 0 "Value: " sumInputs


-----------------
--- Datastore ---
-----------------

infixr 5 .+.

data Schema = SChar | SString | SInt | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SChar = Char
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)

--data DataStore : Type where
--  MkData : (schema : Schema) -> (size : Nat) -> (items : Vect size (SchemaType schema)) -> DataStore

--data Command = Add String | Get Integer | Quit | Size | Search String
data Command : Schema -> Type where
  SetSchema : (newSchema : Schema) -> Command schema
  Add  : SchemaType schema -> Command schema
  Get  : Integer           -> Command schema
  Quit :                      Command schema
  Size :                      Command schema
  List :                      Command schema
  -- TODO: Implement search

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) item = MkData schema _ (f items)
  where
    f : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    f [] = [item]
    f (x :: xs) = x :: f xs

{-
searchStore : (store : DataStore) -> (val : (SchemaType (schema store))) -> SchemaType (schema store)
searchStore (MkData schema _ store) val = f store
  where
    f : Vect m (SchemaType schema) -> (SchemaType schema)
    f {m = Z} [] = ""
    f {m = S l} (x :: xs) = if val `isInfixOf` x then f xs ++ show l ++ ": " ++ x ++ "\n" else f xs
-}
  
getQuoted : List Char -> Maybe (String, String)
getQuoted ('"' :: xs) =
  case span (/= '"') xs of
    (quoted, '"' :: rem) => Just (pack quoted, ltrim $ pack rem)
    _ => Nothing
getQuoted _ = Nothing

getChar : List Char -> Maybe (Char, String)
getChar [] = Nothing
getChar (c :: rem) = Just (c, ltrim $ pack rem)

parsePrefix : (schema : Schema) -> (input : String) -> Maybe (SchemaType schema, String)
parsePrefix SChar input = getChar $ unpack input
parsePrefix SString input = getQuoted $ unpack input
parsePrefix SInt input = 
  case span isDigit input of
    ("", _) => Nothing
    (dig, rem) => Just (cast dig, ltrim rem)
parsePrefix (x .+. y) input = do
  (s1, rem) <- parsePrefix x input
  (s2, rem') <- parsePrefix y rem
  pure ((s1, s2), rem')

parseBySchema : (schema : Schema) -> (input : String) -> Maybe (SchemaType schema)
parseBySchema schema input = 
  case parsePrefix schema input of
    Just (res, "") => Just res
    Just _         => Nothing
    Nothing        => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("Char" :: []) = Just SChar
parseSchema ("Char" :: xs) = parseSchema xs >>= \schem => pure (SChar .+. schem)
parseSchema ("String" :: []) = Just SString
parseSchema ("String" :: xs) = parseSchema xs >>= \schem => pure (SString .+. schem)
parseSchema ("Int" :: []) = Just SInt
parseSchema ("Int" :: xs) = parseSchema xs >>= \schem => pure (SInt .+. schem)
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" rest = map Add (parseBySchema schema rest)
--parseCommand schema "search" val = Just $ Search val
parseCommand schema "get" ""  = Just List
parseCommand schema "get" val = if all isDigit (unpack val) then Just (Get (cast val)) else Nothing
parseCommand schema "quit" "" = Just Quit
parseCommand schema "size" "" = Just Size
parseCommand schema "schema" rest = parseSchema (words rest) >>= pure . SetSchema
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ' ) input of
                   (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SChar} item = "'" ++ cast item ++ "'"
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = (y .+. z)} (itemA, itemB) = display itemA ++ ", " ++ display itemB

setSchema : (store : DataStore) -> (schema : Schema) -> Maybe DataStore
setSchema store schema = case size store of
                              Z => Just $ MkData schema _ []
                              (S k) => Nothing

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
  let storeItems = items store
  in case integerToFin pos (size store) of
           Nothing => Just ("Out of range\n", store)
           Just id => Just (display (index id storeItems) ++ "\n", store)

showStore : (xs : Vect n (SchemaType schema)) -> String
showStore = foldr (\a, b => a ++ "\n" ++ b) "" . map display

showStore' : (xs : Vect n (SchemaType schema)) -> String
showStore' xs = f "" $ map display xs
  where
    f : String -> (ys : Vect m String) -> String
    f {m = Z} res [] = res
    f {m = (S k)} res (y :: ys) = f (show (S k) ++ ": " ++ y ++ "\n" ++ res) ys


listEntries : (store : DataStore) -> Maybe (String, DataStore)
listEntries (MkData schema Z _) = Nothing
listEntries s@(MkData schema _ xs) = Just (showStore' xs, s)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = 
  case parse (schema store) inp of
    Nothing           => Nothing
    Just Quit         => Nothing
    Just (Add item)   => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
    Just (Get x)      => getEntry x store
    Just Size         => Just ("Store size: " ++ show (size store) ++ "\n", store)
    Just List         => listEntries store
    Just (SetSchema schema') => 
      case setSchema store schema' of
        Nothing => Just ("Can't update schema\n", store)
        Just store' => Just ("Store updated!\n", store')
    --(Just (Search val)) => Just (searchStore store val, store)
{-
sto : DataStore
sto = MkData 3 ["One", "Two", "Three"]

res : String
res = searchStore sto "T"

-}
main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput

