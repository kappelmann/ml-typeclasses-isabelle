(*  Title:  lens.ML
    Author: Kevin Kappelmann

Lenses adopted from Haskell's fclables https://hackage.haskell.org/package/fclabels
Unlike fclabels, which uses GADTs and categories, we register lenses as indexed categories.
*)
signature LENS_BASE =
sig
  structure C : CATEGORY_BASE

  (*abstract lens datatype. The getter and modifier operations work in some
  category. The type of the value pointed to might change, thereby changing
  the type of the outer structure.*)
  type ('p1, 't, 'o, 's, 'i) lens
  type ('p1, 's, 'i) getter = ('p1, 's, 'i) C.cat
  type ('p1, 't, 'o, 's, 'i) modifier = ('p1, ('p1, 'i, 'o) C.cat * 's, 't) C.cat
  type ('p1, 's, 'i) slens = ('p1, 's, 'i, 's, 'i) lens
  type ('p1, 's, 'i) smodifier = ('p1, 's, 'i, 's, 'i) modifier

  val lens : ('p1, 's, 'i) getter -> ('p1, 't, 'o, 's, 'i) modifier -> ('p1, 't, 'o, 's, 'i) lens

  val get : ('p1, 't, 'o, 's, 'i) lens -> ('p1, 's, 'i) getter
  val modify : ('p1, 't, 'o, 's, 'i) lens -> ('p1, 't, 'o, 's, 'i) modifier

  include ICATEGORY_BASE
  sharing type cat = lens
end

functor Lens_Base(AA : ARROW_APPLY) : LENS_BASE =
struct

structure A = Arrow(AA)
structure C = AA

type ('p1, 's, 'i) getter = ('p1, 's, 'i) C.cat
type ('p1, 't, 'o, 's, 'i) modifier = ('p1, ('p1, 'i, 'o) C.cat * 's, 't) C.cat
type ('p1, 's, 'i) smodifier = ('p1, 's, 'i, 's, 'i) modifier

datatype ('p1, 't, 'o, 's, 'i) lens = Lens of {
  get : ('p1, 's, 'i) getter,
  modify : ('p1, 't, 'o, 's, 'i) modifier
}
type ('p1, 's, 'i) slens = ('p1, 's, 'i, 's, 'i) lens

fun lens get modify = Lens {get = get, modify = modify}

fun get (Lens {get, ...}) = get
fun modify (Lens {modify, ...}) = modify

type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) lens

fun id _ = lens (A.id ()) AA.app

fun comp l1 l2 =
  let
    val g1 = get l1
    val m1 = modify l1
    val g2 = get l2
    val m2 = modify l2
  in lens (A.comp g1 g2) (AA.uncurry (A.curry m2 o A.curry m1)) end

end

signature LENS =
sig
  include LENS_BASE

  type ('p1, 't, 's, 'o) setter = ('p1, ('o * 's), 't) C.cat
  type ('p1, 's, 'o) ssetter = ('p1, ('o * 's), 's) C.cat

  val set : ('p1, 't, 'o, 's, 'i) lens -> ('p1, 't, 's, 'o) setter

  val lens_get : ('p1, 's, 'i) C.cat -> ('p1, 'o, 'o, 's, 'i) lens
  val lens_modify : ('p1, 'o, 't) C.cat -> ('p1, 't, 'o, 'i, 'i) lens
  val lens_get_modify : ('p1, 's, 'i) C.cat -> ('p1, 'u, 'o) C.cat -> ('p1, 'o, 'u, 's, 'i) lens

  (*pairs*)
  val get_fst : ('p1, 's, 'i1 * 'i2) getter -> ('p1, 's, 'i1) getter
  val get_snd : ('p1, 's, 'i1 * 'i2) getter -> ('p1, 's, 'i2) getter
  val modify_fst : ('p1, 't, 'o1 * 'i2, 's, 'i1 * 'i2) modifier -> ('p1, 't, 'o1, 's, 'i1) modifier
  val modify_snd : ('p1, 't, 'i1 * 'o2, 's, 'i1 * 'i2) modifier -> ('p1, 't, 'o2, 's, 'i2) modifier
  val lens_fst : ('p1, 't, 'o1 * 'i2, 's, 'i1 * 'i2) lens -> ('p1, 't, 'o1, 's, 'i1) lens
  val lens_snd : ('p1, 't, 'i1 * 'o2, 's, 'i1 * 'i2) lens -> ('p1, 't, 'o2, 's, 'i2) lens
end

functor Lens(structure A : ARROW; structure L : LENS_BASE sharing type L.C.cat = A.cat) : LENS =
struct

open L

type ('p1, 't, 's, 'o) setter = ('p1, ('o * 's), 't) C.cat
type ('p1, 's, 'o) ssetter = ('p1, ('o * 's), 's) C.cat

fun set l = C.comp (modify l) (A.first (A.arr A.K))

fun lens_get f =
  L.lens (L.id () |> L.get |> L.C.comp f) (A.second f |> L.C.comp (L.modify (L.id ())))

fun lens_modify f =
  let val id = L.id ()
  in L.lens (L.get id) (L.C.comp f (L.modify id)) end

fun lens_get_modify get modify = lens_get get |> comp (lens_modify modify)

(*pairs*)
fun get_fst f = C.comp (A.arr fst) f
fun get_snd f = C.comp (A.arr snd) f
fun modify_fst f = C.comp f (A.first (A.arr A.first))
fun modify_snd f = C.comp f (A.first (A.arr A.second))

fun lens_fst l = lens (get_fst (get l)) (modify_fst (modify l))
fun lens_snd l = lens (get_snd (get l)) (modify_snd (modify l))

end

signature LENS_PAIR =
sig
  include LENS_BASE
  val get_pair :
    ('p1, 's1, 'i1) getter -> ('p1, 's2, 'i2) getter -> ('p1, 's1 * 's2, 'i1 * 'i2) getter
  val modify_pair : ('p1, 's1 * 's2, 'i1 * 'i2) getter ->
    ('p1, 't1, 'o1, 's1, 'i1) modifier -> ('p1, 't2, 'o2, 's2, 'i2) modifier ->
    ('p1, 't1 * 't2, 'o1 * 'o2, 's1 * 's2, 'i1 * 'i2) modifier
  val lens_pair : ('p1, 't1, 'o1, 's1, 'i1) lens -> ('p1, 't2, 'o2, 's2, 'i2) lens ->
    ('p1, 't1 * 't2, 'o1 * 'o2, 's1 * 's2, 'i1 * 'i2) lens
end

functor Lens_Pair(
    structure A : ARROW
    structure AA : ARROW_APPLY_BASE
    sharing type AA.cat = A.cat
    structure L : LENS_BASE
    sharing type L.C.cat = A.cat
  ) : LENS_PAIR =
struct

open L

local structure SC = Semi_Category(A) open SC A
in
fun get_pair g1 g2 = g1 *** g2

fun modify_pair g m1 m2 =
  arr (fn (f, x) => ((f, x), x))
  >>> first (second g >>> AA.app >>> arr (SArrow_Apply.*** (K #> pair, K #> pair)))
  >>> arr (uncurry SArrow_Apply.***)
  >>> (m1 *** m2)

fun lens_pair l1 l2 =
  let val g = get_pair (L.get l1) (L.get l2)
  in L.lens g (modify_pair g (L.modify l1) (L.modify l2)) end
end

end