/-- A class for categories. Instances should satisfy the laws

Right identity
    `f . id = f`

Left identity
    `id . f = f`

Associativity
    `f . (g . h) = (f . g) . h`

 See <https://hackage.haskell.org/package/base-4.20.0.1/docs/Control-Category.html#t:Category>
 and <https://wiki.haskell.org/Arrow_tutorial>

-/
class Category (cat : k -> k -> Type u)
where
  /-- The identity morphism  -/
  id {a:k}: cat a a
  /-- Morphism composition  -/
  compose {b c a :k}: cat b c → cat a b → cat a c

instance : Category (. -> .) where
  id := id
  compose := (. ∘ .)

/-- Right-to-left composition  -/
infixr:90 " <<< " => Category.compose
/-- Left-to-right composition  -/
infixr:90 " >>> " => fun x y => Category.compose y x
recommended_spelling "compose" for "<<<" in [Category.compose, «term_<<<_»]
recommended_spelling "compose" for ">>>" in [Category.compose, «term_>>>_»]

#check (id ∘ id : Nat → Nat)
#check (id <<< id : Category (. → .))
#check (id >>> id : Category (. → .))

/-- The basic arrow class.

### Laws
Instances should satisfy the following laws:
`arr id = id`
`arr (f >>> g) = arr f >>> arr g`
`first (arr f) = arr (first f)`
`first (f >>> g) = first f >>> first g`
`first f >>> arr fst = arr fst >>> f`
`first f >>> arr (id *** g) = arr (id *** g) >>> first f`
`first (first f) >>> arr assoc = arr assoc >>> first f`

where

`assoc ((a,b),c) = (a,(b,c))`

The other combinators have sensible default definitions, which may be overridden for efficiency.
### Minimal complete definition
`arr, (first | merge)

See <https://hackage.haskell.org/package/base-4.20.0.1/docs/Control-Arrow.html>
-/

class Arrow (a : Type u -> Type u -> Type w) extends Category a where
  /-- Lift a function to an arrow. -/
  arr : (b -> c) -> a b c
  /-- Send the first component of the input through the argument arrow, and copy the rest unchanged to the output.
  ```txt
  b -> c
  d -> d
  ```
  ### Default implementation
  `(*** id)`
  -/
  first : a b c -> a (b × d) (c × d)
  /-- A mirror image of `first`.
  ```txt
  d -> d
  b -> c
  ```
  ### Default implementation
  `(id ***)`
  -/
  second : a b c -> a (d × b) (d × c) :=
    (fun f g => (first f >>> arr Prod.swap >>> first g >>> arr Prod.swap)) id

  /-- Map two elements in parallel.

  Split the input between the two argument arrows and combine their output. Note that this is in general not a functor. Also called `f *** g`
  ```txt
  b -> f -> c
  b' -> g -> c'
  ```
  ### Default implementation
  `first f >>> arr swap >>> first g >>> arr swap`
  -/
  merge (f: a b c) (g: a b' c') : a (b × b') (c × c') :=
    first f >>> arr Prod.swap >>> first g >>> arr Prod.swap
  /-- Send input to both argument arrows and combine their output. Also called `f &&& g`.
  ```txt
     |-> f -> c
  b -|
     |-> g -> c'
  ```
  ### Default implementation
  `arr (λb ↦ (b,b)) >>> f *** g`
  -/
  split (f: a b c) (g: a b c') : a b (c × c') :=
    arr (λb ↦ (b,b)) >>> merge f g

infixr:90 " *** " => Arrow.merge
infixr:90 " &&& " => Arrow.split
recommended_spelling "merge" for "***" in [Arrow.merge, «term_***_»]
recommended_spelling "split" for "&&&" in [Arrow.split, «term_&&&_»]

def returnA [Arrow a]: a b b := Category.id

instance : Arrow (· -> ·) where
  arr := id
  first f := fun (a, x) => (f a, x)


-- TODO is arrow notation worth implementing?
-- ≺≻ looks like arrow notation?
