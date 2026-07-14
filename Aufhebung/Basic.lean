import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

open CategoryTheory

universe u v

/-- An **idempotent monad** on `C`: a monad whose object-action is strictly
idempotent, `□□X = □X`. Extends Mathlib's `CategoryTheory.Monad`. -/
structure IdempotentMonad (C : Type u) [Category.{v} C] extends CategoryTheory.Monad C where
  /-- Strict idempotence on objects: `□(□X) = □X`. -/
  obj_idem : ∀ X, obj (obj X) = obj X

/-- An **idempotent comonad** on `C`: a comonad whose object-action is strictly
idempotent, `□□X = □X`. Extends `CategoryTheory.Comonad`. -/
structure IdempotentComonad (C : Type u) [Category.{v} C] extends CategoryTheory.Comonad C where
  /-- Strict idempotence on objects: `□(□X) = □X`. -/
  obj_idem : ∀ X, obj (obj X) = obj X

/-- A `Moment` on `C` is an idempotent monad or an idempotent comonad. -/
inductive Moment (C : Type u) [Category.{v} C]
  | monad   : IdempotentMonad C → Moment C
  | comonad : IdempotentComonad C → Moment C

namespace Moment

variable {C : Type u} [Category.{v} C]

/-- The action of a moment on objects, written `□`. -/
def obj : Moment C → C → C
  | .monad T   => T.obj
  | .comonad G => G.obj

/-- The underlying endofunctor `□ : C ⥤ C` of a moment. -/
def functor : Moment C → (C ⥤ C)
  | .monad T   => T.toMonad.toFunctor
  | .comonad G => G.toComonad.toFunctor

/-- Every moment is strictly idempotent: `□□X = □X`. -/
theorem idem : ∀ (M : Moment C) (X : C), M.obj (M.obj X) = M.obj X
  | .monad T,   X => T.obj_idem X
  | .comonad G, X => G.obj_idem X

/-- `Y` lies in the **image** of the moment: `Y = □X` for some `X`. -/
def InImage (M : Moment C) (Y : C) : Prop := ∃ X, Y = M.obj X

/-- `Y` is **invariant** — "purely of that moment": `□Y = Y`. -/
def Invariant (M : Moment C) (Y : C) : Prop := M.obj Y = Y

/-- **Due to idempotency, image = invariant:** `Y = □X ⇔ □Y = Y`. -/
theorem inImage_iff_invariant (M : Moment C) (Y : C) :
    M.InImage Y ↔ M.Invariant Y := by
  constructor
  · rintro ⟨X, rfl⟩
    exact M.idem X
  · intro h
    exact ⟨Y, h.symm⟩

/-- The invariant objects span a full subcategory `C□ ⊆ C`. -/
abbrev InvariantSubcategory (M : Moment C) : Type _ :=
  ObjectProperty.FullSubcategory M.Invariant

/-- `C□` is a category, with morphisms inherited from `C`. -/
example (M : Moment C) : Category.{v} M.InvariantSubcategory := inferInstance

/-- The inclusion `C□ ⥤ C`. -/
def InvariantSubcategory.ι (M : Moment C) : M.InvariantSubcategory ⥤ C :=
  ObjectProperty.ι M.Invariant

/-! ### Two concrete moments on the category of types -/

/-- The ambient universe of types, as a category (objects are types in `Type u`,
morphisms are functions). -/
abbrev U := Type u

/-- The **unit moment** on `Type u`: every type `X` maps to the unit type
`PUnit`. A (computable) idempotent monad — every law holds because any two
functions *into* `PUnit` agree. -/
def unitType : Moment U :=
  .monad
    { obj := fun _ => PUnit.{u+1}
      map := fun _ => 𝟙 _
      map_id := by intros; ext x
      map_comp := by intros; ext x
      η := { app := fun _ => TypeCat.ofHom (fun _ => PUnit.unit)
             naturality := by intros; ext x }
      μ := { app := fun _ => 𝟙 _
             naturality := by intros; ext x }
      assoc := by intros; ext x
      left_unit := by intros; ext x
      right_unit := by intros; ext x
      obj_idem := fun _ => rfl }

/-- The **bottom moment** on `Type u`: every type `X` maps to the empty type
`PEmpty`. A (computable) idempotent comonad — every law holds because any two
functions *out of* `PEmpty` agree (vacuously). -/
def bottomType : Moment U :=
  .comonad
    { obj := fun _ => PEmpty.{u+1}
      map := fun _ => 𝟙 _
      map_id := by intros; ext x; exact x.elim
      map_comp := by intros; ext x; exact x.elim
      ε := { app := fun _ => TypeCat.ofHom (fun e => e.elim)
             naturality := by intros; ext x; exact x.elim }
      δ := { app := fun _ => 𝟙 _
             naturality := by intros; ext x; exact x.elim }
      coassoc := by intros; ext x; exact x.elim
      left_counit := by intros; ext x; exact x.elim
      right_counit := by intros; ext x; exact x.elim
      obj_idem := fun _ => rfl }

/-- **The two moments are adjoint.** The bottom moment (constant `⊥ = PEmpty`) is
*left* adjoint to the unit moment (constant `⊤ = PUnit`):
`Hom(⊥, Y) ≅ Hom(X, ⊤)`, since both sides are singletons. The unit `η_X : X ⟶ ⊤`
and counit `ε_Y : ⊥ ⟶ Y` are the unique such maps, and both triangle identities
hold automatically (every hom into `⊤` / out of `⊥` is unique). -/
def bottomAdjUnit : bottomType.functor ⊣ unitType.functor where
  unit := { app := fun _ => TypeCat.ofHom (fun _ => PUnit.unit)
            naturality := by intros; ext x; exact Subsingleton.elim _ _ }
  counit := { app := fun _ => TypeCat.ofHom (fun e => e.elim)
              naturality := by intros; ext x; exact x.elim }
  left_triangle_components := by intro X; ext x; exact x.elim
  right_triangle_components := by intro Y; ext x; exact Subsingleton.elim _ _

end Moment
