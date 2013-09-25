if = \(T: Set) (b: Bool) (t: T) (f: T) -> 
  elim Bool (\(_: Bool) -> T) f t b;

{- 
A naive implementation of a check if a list is a sublist of another can be coded 
in Haskell as shown in 'kmp_hs.hs'.
Trying to convert it to TTlite, we can first inline 'n' inside 'm', and then notice
that 'm' is structurally recursive on the pair (os, pp). So, we can encode it in 
TTlite with 2 nested recursions - 'isSublist_aux1' (inner recursion on 'pp') 
and 'isSublist_aux2' (outer recursion on 'os'):
-}

isSublist_aux1 = \ (T: Set) (T_eq: forall (_: T) (_: T). Bool) (b: Bool) (pp: List T) (ss: List T) (op: List T) -> 
  elim (List T) (\ (_ : List T) -> forall (_: List T) (_: List T). Bool)
    (\ (_: List T) (_: List T) -> True)
    (\ (p : T) (pp : List T) (IHpp : forall (_: List T) (_: List T). Bool) (ss: List T) (op: List T) ->
      elim (List T) (\ (_ : List T) -> forall (_: List T). Bool)
        (\ (_ : List T) -> False)
        (\ (s : T) (ss : List T) (_ : forall (_: List T). Bool) (op : List T) -> 
          if Bool (T_eq p s) (IHpp ss op) b)
        ss op)
    pp ss op;
    
isSublist_aux2 = \ (T: Set) (T_eq: forall (_: T) (_: T). Bool) (pp: List T) (ss: List T) (op: List T) (os: List T) ->     
  elim (List T) (\ (_ : List T) -> forall (_: List T) (_: List T) (_: List T) . Bool)
   (isSublist_aux1 T T_eq False)
   (\ (_ : T) (os : List T) (IHos : forall (_: List T) (_: List T) (_: List T) . Bool) ->
     isSublist_aux1 T T_eq (IHos op os op))
   os pp ss op;
   
isSublist = \(T: Set) (T_eq: forall (_: T) (_: T). Bool) (p: List T) (s: List T) -> 
  isSublist_aux2 T T_eq p s p s;
              
listTTF = Cons (List Bool) True (Cons (List Bool) True (Cons (List Bool) False (Nil (List Bool))));

listTTTF = Cons (List Bool) True listTTF;

eqBool = \(b1: Bool) (b2: Bool) -> if Bool b1 b2 (if Bool b2 False True);

isSublist_test1 : Id Bool (isSublist Bool eqBool listTTF listTTTF) True;
isSublist_test1 = Refl Bool True;

{-
$l: List Bool;

t = mrsc (isSublist Bool eqBool listTTF $l);
-}     
   