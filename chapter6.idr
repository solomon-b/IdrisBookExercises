module Chapter6
  
import Data.Vect

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety Four"
getStringOrInt True = 94
  
valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False = trim 
valToString True  = cast

valToString' : (isInt : Bool) -> (case isInt of 
                                       False => String
                                       True => Int) -> String
valToString' False x = trim x
valToString' True x = cast x
  
AdderType : (numArgs : Nat) -> Type
AdderType Z = Int
AdderType (S k) = (next : Int) -> AdderType k

adder : (numArgs : Nat) -> (acc : Int) -> AdderType numArgs
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

data Format = Number Format 
            | Str Format 
            | Chr Format
            | Dbl Format
            | Lit String Format 
            | End
  
PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Chr fmt) = (chr : Char) -> PrintfType fmt
PrintfType (Dbl fmt) = (dbl : Double) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \n => printfFmt fmt (acc ++ show n)
printfFmt (Str fmt) acc = \str  => printfFmt fmt (acc ++ str)
printfFmt (Chr fmt) acc = \char => printfFmt fmt (acc ++ show char)
printfFmt (Dbl fmt) acc = \dbl  => printfFmt fmt (acc ++ show dbl)
printfFmt (Lit str fmt) acc =      printfFmt fmt (acc ++ str)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dbl (toFormat chars)
toFormat (c   ::        chars) = case toFormat chars of
                                     Lit lit chars' => Lit (strCons c lit) chars'
                                     fmt            => Lit (strCons c "") fmt 

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

  
Matrix : Nat -> Nat -> Type
Matrix k j = Vect k (Vect j Double)
  
testMatrix : Matrix 2 3
testMatrix = [[0,0,0], [0,0,0]]

TupleVect : Nat -> (ty : Type) -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1,2,3,4,())
