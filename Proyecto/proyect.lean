
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-Pruebas creando clases (ejemplos que aparecen en mathematics in Lean)-/
class One₁ (α : Type) where
  one : α
class Dia1 (α : Type) where
  dia : α →  α →  α
infixl:70 "⋄" => Dia1.dia


class Semigroup1 (α : Type) where
  toDia1 : Dia1 α
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

class Groupp (α : Type _) where
  mul: α → α → α
  one : α
  inv: α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

/-class RealField, creada con de ayuda de  GPT (garantizar que funcione, fallaba con la sintaxis)-/


/-se extiende la clase de LinearOrderedField, ya implementada en Mathlib
     . R es de tipo LinearOrderedField, y queremos añadirle propiedad del supremo.

      Dado s subconjunto no vacío y acotado por arriba, queremos una aplicación (Sup): sets R → R,
      tal que sup s sea una cota superior de s y que dada r (cota superior arbitraria de s),
      Sup s ≤ r
-/


class RealField (R : Type _) extends LinearOrderedField  R where
  Sup : (s : Set R) → (s.Nonempty ∧ ∃ b, ∀ x ∈ s, x ≤ b) → R
  Sup_cond: ∀( s : Set R )(h : s.Nonempty ∧ ∃ b, ∀ x ∈ s, x ≤ b),
      (∀ x ∈ s, x ≤ Sup s h) ∧  ∀ y, (∀ x ∈ s, x ≤ y) → Sup s h ≤ y

variable {s: Type _}
variable (v : RealField s)
