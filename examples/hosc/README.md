This directory contains examples from the paper

* Ilya Klyuchnikov and Sergei Romanenko.
**Proving the Equivalence of Higher-Order Terms by Means of Supercompilation**.
In: Proceedings of the Seventh International Andrei Ershov Memorial Conference: Perspectives of System Informatics.
LNCS 5947. 2010. [pdf](http://hosc.googlecode.com/files/Klyuchnikov__Romanenko_Proving_the_Equivalence_of_Higher_Order_Terms_by_Means_of_Supercompilation.pdf)

The definitions given in the paper are:

    data List a = Nil | Cons a (List a)
    data Boolean = True | False
    data Pair a b = Pair a b

    compose =
        \f g x -> f (g x)

    unit =
        \x -> Cons x Nil

    rep =
        \xs -> append xs

    abs =
        \f -> f Nil
	
    fp =
        \p1 p2 ->
            case p1 of Pair f1 f2 ->
                case p2 of Pair x1 x2 -> P (f1 x1) (f2 x2)

    map =
        \f xs ->
            case xs of
                Nil -> Nil
                Cons x1 xs1 -> Cons (f x1) (map f xs1)

    append = \xs ys ->
        case xs of
            Nil -> ys
            Cons x1 xs1 -> Cons x1 (append xs1 ys)

    join =
        \xs ->
            case xs of
                Nil -> Nil
                Cons x1 xs1 -> append x1 (join xs1)

    idList =
        \xs ->
            case xs of
                Nil -> Nil
                Cons x1 xs1 -> Cons x1 (idList xs1)

    filter =
        \p xs ->
            case xs of
                Nil -> Nil
                Cons x xs1 ->
                    case p x of
                        True -> Cons x (filter p xs1)
                        False -> filter p xs1

    zip =
		\p -> 
            case p of Pair xs ys ->
                case xs of
                Nil -> Nil
                    Cons x1 xs1 ->
                        case ys of
                            Nil -> Nil
                            Cons y1 ys1 -> Cons (P x1 y1) (zip (P xs1 ys1))
                      		
The following equivalences are proved in the paper:

* 01.hs `compose (map f) unit x = compose unit f x`
* 02.hs `compose (map f) join xs = compose join (map (map f)) xs`
* 03.hs `append (map f xs) (map f ys) = map f (append xs ys)`
* 04.hs `filter p (map f xs) = map f (filter (compose p f) xs)`
* 05.hs `map (compose f g) xs = (compose (map f)(map g)) xs`
* 06.hs `rep (append xs ys) zs = (compose (rep xs) (rep ys)) zs`
* 07.hs `(compose abs rep) xs = idList xs`
* 08.hs `map (fp (P f g)) (zip (P x y)) = zip (fp (P (map f) (map g)) (P x y))`
* 09.hs `append r (Cons p ps) = case (append r (Cons p Nil)) of {Nil -> ps; Cons v vs -> Cons v (append vs ps)}`

TT Lite is able to prove all of them except 4 and 8. 4 is not proved since it requires generalization:
during supercompilation the term `case (p x) of ...` is encountered, and HOSC extracts in this case `p x`.
8 requires more folding on renaming and corresponding code generator.

There are other interestin proved equivalences:

* 10.hs `plus x (plus y z) = plus (plus x y) z`
* 11.hs `append x (append y z) = append (append x y) z`
* 12.hs `unchurch (churchPlus (church x) (church y)) = nat_id (plus x y)`


