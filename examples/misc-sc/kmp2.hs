import "examples/id.hs";
import "examples/product.hs";

-- shortcuts
nil = Nil (List Bool);
cons = \ (h : Bool) (t : List Bool) -> Cons (List Bool) h t;
if = \ (b: Bool) (t: Bool) (f: Bool) -> elim Bool (\(_: Bool) -> Bool) f t b;
eq = \ (b1: Bool) (b2: Bool) -> if b1 (if b2 True False) (if b2 False True);
string = List Bool;
$s : string;

-- test strings
f = cons False nil;
t = cons True nil;
ff = cons False f;
tt = cons True t;
tf = cons True f;
ttf = cons True tf;

empty : forall (s : string) . Bool;
empty = \(s : string) ->
    elim (List Bool)
        (\(_ : string) -> Bool)
        True
        (\(_ : Bool)(_ : string)(xs : Bool) -> False)
        s;

-- tests that p is a prefix of s
prefix : forall (p : string) (s : string) . Bool;
prefix =
    \(p : string) ->
        elim (List Bool)
            (\(_ : string) -> forall (s : string) . Bool)
            (\(_ : string) -> True)
            (\(ph : Bool)(p1 : string)(prefix : forall (_ : string) . Bool)(s : string) ->
                elim (List Bool)
                    (\ (_ : string) -> Bool)
                    False
                    (\ (sh : Bool) (s1 : string)(_ : Bool) -> if (eq ph sh) (prefix s1) False)
                    s)
            p;

prefix_test_1 : Id Bool (prefix t f) False;
prefix_test_1 = Refl Bool False;

prefix_test_2 : Id Bool (prefix t t) True;
prefix_test_2 = Refl Bool True;

prefix_test_3 : Id Bool (prefix t tt) True;
prefix_test_3 = Refl Bool True;

prefix_test_4 : Id Bool (prefix tt t) False;
prefix_test_4 = Refl Bool False;

-- tests that p is a substring of s
match = \(p : string)(s : string) ->
    elim (List Bool)
        (\(_ : string) -> Bool)
        (empty p)
        (\(h : Bool)(t : string)(r: Bool) -> if (prefix p (cons h t)) True r)
        s;

match_test_1 : Id Bool (match t f) False;
match_test_1 = Refl Bool False;

match_test_2 : Id Bool (match t t) True;
match_test_2 = Refl Bool True;

match_test_3 : Id Bool (match f ttf) True;
match_test_3 = Refl Bool True;

match_test_3 : Id Bool (match tf ttf) True;
match_test_3 = Refl Bool True;

e1 = match ff $s;
(r1, _) = sc e1;

e2 = prefix ff $s;
(r2, _) = sc e2;

pr2 =
    \(s : string) ->
        elim (List Bool) (\ (_ : List Bool) -> Bool)
            False
            (\ (a : Bool) (b : List Bool) (_ : Bool) ->
                elim Bool
                (\ (_ : Bool) -> Bool)
                (elim (List Bool) (\ (_ : List Bool) -> Bool)
                    False
                    (\ (d : Bool) (_ : List Bool) (_ : Bool) ->
                        elim Bool (\ (_ : Bool) -> Bool)
                            True
                            False
                            d)
                    b)
                False
                a)
        s;

fstb = fst Bool Bool;
sndb = snd Bool Bool;

fg1 =
    \ (s : string) ->
        elim (List Bool)
            (\ (_ : List Bool) -> Product Bool Bool)
            (Pair (Product Bool Bool) False False)
            (\ (c : Bool) (s : string) (r : Product Bool Bool) ->
                elim Bool
                    (\ (_ : Bool) -> Product Bool Bool)
                    -- F
                    (Pair (Product Bool Bool) (sndb r) True)
                    -- T
                    (Pair (Product Bool Bool) (fstb r) (fstb r))
                    c)
            s;

match1 = \ (s : string) -> fstb (fg1 s);

z1 = match1 nil;
z2 = match1 ff;

pair_get = forall (_ : Bool) (_ : Bool) . Bool;
product = forall (get : pair_get) . Bool;

pair : forall (x : Bool) (y : Bool) . product;
pair = \ (x : Bool) (y : Bool) (get : pair_get) -> get x y;

fstc  = \(p : product) -> p (\(x : Bool)(y : Bool) -> x);
sndc  = \(p : product) -> p (\(x : Bool)(y : Bool) -> y);


fg2 =
    \ (s : string) ->
        elim (List Bool)
            (\ (_ : List Bool) -> product)
            (pair False False)
            (\ (c : Bool) (s : string) (r : product) ->
                elim Bool
                    (\ (_ : Bool) -> product)
                    -- F
                    (pair (sndc r) True)
                    -- T
                    (pair (fstc r) (fstc r))
                    c)
            s;

match2 = \ (s : string) -> fstc (fg2 s);

y1 = match2 nil;
y2 = match2 ff;

$c1 : Bool;
$c2 : Bool;

e3 = match2 (cons $c1 (cons $c2 nil));
(r3, _) = sc e3;

e4 = match ff (cons $c1 (cons $c2 nil));
(r4, _) = sc e4;
