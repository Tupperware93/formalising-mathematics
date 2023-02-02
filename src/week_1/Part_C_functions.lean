import tactic

-- injective and surjective functions are already in Lean.
-- They are called `function.injective` and `function.surjective`.
-- It gets a bit boring typing `function.` a lot so we start
-- by opening the `function` namespace

open function

-- We now move into the `xena` namespace

namespace xena

-- let X, Y, Z be "types", i.e. sets, and let `f : X → Y` and `g : Y → Z`
-- be functions

variables {X Y Z : Type} {f : X → Y} {g : Y → Z}

-- let a,b,x be elements of X, let y be an element of Y and let z be an
-- element of Z

variables (a b x : X) (y : Y) (z : Z)

/-!
# Injective functions
-/

-- let's start by checking the definition of injective is
-- what we think it is.

lemma injective_def : injective f ↔ ∀ a b : X, f a = f b → a = b :=
begin
  -- true by definition
  refl
end

-- You can now `rw injective_def` to change `injective f` into its definition.

-- The identity function id : X → X is defined by id(x) = x. Let's check this

lemma id_def : id x = x :=
begin
  -- true by definition
  refl
end

-- you can now `rw id_def` to change `id x` into `x`

/-- The identity function is injective -/
lemma injective_id : injective (id : X → X) :=
begin
  intros a b h,
  exact h,
end

-- function composition g ∘ f is satisfies (g ∘ f) (x) = g(f(x)). This
-- is true by definition. Let's check this

lemma comp_def : (g ∘ f) x = g (f x) :=
begin
  -- true by definition
  refl
end

/-- Composite of two injective functions is injective -/
lemma injective_comp (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  -- you could start with `rw injective_def at *` if you like.
  -- In some sense it doesn't do anything, but it might make you happier.
  intros a b h,
  apply hf, 
  apply hg,
  exact h,
end

/-!

### Surjective functions

-/

-- Let's start by checking the definition of surjectivity is what we think it is

lemma surjective_def : surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
begin
  -- true by definition
  refl
end

/-- The identity function is surjective -/
lemma surjective_id : surjective (id : X → X) :=
begin
  -- you can start with `rw surjective_def` if you like.
  intro b,
  use b,
  refl,
end

-- If you started with `rw surjective_def` -- try deleting it.
-- Probably your proof still works! This is because
-- `surjective_def` is true *by definition*. The proof is `refl`.

-- For this next one, the `have` tactic is helpful.

/-- Composite of two surjective functions is surjective -/
lemma surjective_comp (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  intro c,
  obtain ⟨b,h⟩ := hg c,
  obtain ⟨a,h'⟩ := hf b,
  use a, 
  dsimp,
  rwa [h'],
end

/-!

### Bijective functions

In Lean a function is defined to be bijective if it is injective and surjective.
Let's check this.

-/

lemma bijective_def : bijective f ↔ injective f ∧ surjective f :=
begin
  -- true by definition
  refl
end

-- You can now use the lemmas you've proved already to make these
-- proofs very short.

/-- The identity function is bijective. -/
lemma bijective_id : bijective (id : X → X) :=
begin
  exact ⟨injective_id, surjective_id⟩,
end

/-- A composite of bijective functions is bijective. -/
lemma bijective_comp (hf : bijective f) (hg : bijective g) : bijective (g ∘ f) :=
begin
  refine ⟨injective_comp _ _, surjective_comp _ _⟩,
  exact hf.left,
  exact hg.left,
  exact hf.right,
  exact hg.right,
end

end xena
