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
  
data Schema = SString | SInt | (.+.) Schema Schema

SchemaType : Schema -> Type
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
  Add  : SchemaType schema -> Command schema
  Get  : Integer           -> Command schema
  Quit :                      Command schema

--size : DataStore -> Nat
--size (MkData _ size' _) = size'
--  
--schema : DataStore -> Schema
--schema (MkData schema' _ _) = schema'

--items : (store : DataStore) -> Vect (size store) (SchemaType (schema store))
--items (MkData _ _ items') = items'

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

parseBySchema : (schema : Schema) -> (input : String) -> Maybe (SchemaType schema)
parseBySchema schema input = case _ of
                                  case_val => ?parseBySchema_rhs

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
--parseCommand schema "add" rest = Just $ Add ((parseBySchema schema rest) rest)
parseCommand schema "add" rest = 
  case parseBySchema schema rest of
    Just rest' => Just $ Add rest'
    Nothing => Nothing
--parseCommand schema "search" val = Just $ Search val
parseCommand schema "get" val = if all isDigit (unpack val) then Just (Get (cast val)) else Nothing
parseCommand schema "quit" "" = Just Quit
--parseCommand schema "size" "" = Just Size
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ' ) input of
                   (cmd, args) => parseCommand schema cmd (ltrim args)
  
display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = (y .+. z)} (itemA, itemB) = display itemA ++ ", " ++ display itemB


getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = 
  let storeItems = items store 
  in case integerToFin pos (size store) of
           Nothing => Just ("Out of range\n", store)
           Just id => Just (display (index id storeItems) ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = 
  case parse (schema store) inp of
    Nothing             => Nothing
    (Just Quit)         => Nothing
    (Just (Add item))   => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
    (Just (Get x))      => getEntry x store
    --(Just Size)         => Just ("Store size: " ++ show (size store) ++ "\n", store)
    --(Just (Search val)) => Just (searchStore store val, store)
{-
sto : DataStore
sto = MkData 3 ["One", "Two", "Three"]

res : String
res = searchStore sto "T"

-}  
main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput

