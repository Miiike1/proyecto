import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

def Continuous_at_in (f : ℝ → ℝ) (x : ℝ) (s : Set ℝ) :=  ∀ ε : ℝ , ε >0 → ∃ δ : ℝ, δ > 0 ∧ (∀ y ∈ s, |x - y| < δ  → |f x - f y| < ε)
def Continuous_on (f : ℝ → ℝ) (s : Set ℝ) := ∀ x ∈ s, Continuous_at_in f x s

lemma abs_leq_iff_leq_leq (a b : ℝ) : (|a| < b)↔(-b < a) ∧ (a < b) := by exact abs_lt

lemma abs_sub_less : ∀(x y z : ℝ),(z > 0) → (y ≤ x) → (x-z < y)→ |x - y| < z:= by
    intro x y z  h1 h2 h3
    rw[abs_leq_iff_leq_leq]
    constructor
    ·   linarith
    ·   linarith

--este con chat GPT entero, lo metí por probar y salió

lemma abs_sub_neg_pos_le_abs (a b : ℝ) (ha : a < 0) (hb : b > 0) :|a - b| ≥ |a| := by
  have ha' : |a| = -a := by rw [abs_of_neg ha]
  have hab : a - b < 0 := by linarith
  rw [abs_of_neg hab, ha']
  linarith








theorem Bolzano (f:ℝ → ℝ) (a b:ℝ) (h:a < b):(Continuous_on f (Set.Icc a b)) → ((f a)*(f b)<0) →( ∃ x ∈ Set.Icc a b, f x = 0) := by

    intro cont_f
    intro extremos
    let s := {x ∈ Set.Icc a b | f x * f a > 0}
    have hs:a ∈ s:= by
        constructor
        .   have h1:a <= a := by
               exact le_refl a
            exact Set.mem_Icc.mpr ⟨h1, h.le⟩
        . have n_zero:¬ (f a = 0):=by
            intro contra
            rw [contra] at extremos
            have cero:0*f b = 0 := by
                exact zero_mul (f b)
            rw [cero] at extremos
            exact LT.lt.false extremos
            --have neg: (f a) * (f a) < 0 := by
          --have pos: (f a) * (f a) > 0 := by
          simp [n_zero]
    let Nonempty_s: s.Nonempty := by
        use a
    let BddAboved_s: BddAbove s:= by
        use b
        intro x hx
        exact hx.left.right
    obtain ⟨sup,hsup ⟩ := Real.exists_isLUB  Nonempty_s  BddAboved_s

    have pos:=lt_trichotomy ((f sup)*(f a)) 0
    --cases' pos with pos_lt pos1_aux
    rcases pos with (pos_lt | pos_eq | pos_gt)
    ·   exfalso
-- Para extructurarlo: (f x) * (f a) es continua
--                     si g es  continua y g x < 0, g x es menor que 0 en un entorno de x
--                     si g x > 0, g x es mayor que 0 en un entorno de x
        unfold IsLUB at hsup
        unfold IsLeast at hsup
        have cont_g:Continuous_at_in (fun x => f x * f a) sup s:= by
            intro ε ε_pos
            unfold Continuous_on at cont_f
            unfold Continuous_at_in at cont_f
            specialize cont_f sup
            have fa_ne_zero: f a ≠ 0 := by
                intro contra
                rw[contra] at extremos
                rw[zero_mul (f b)] at extremos
                exfalso
                exact (lt_self_iff_false 0).mp extremos
            have abs_fa_pos: |f a| > 0 := by
                exact abs_pos.mpr fa_ne_zero
            have sup_in_ab: sup ∈ Set.Icc a b := by
                constructor
                .   have h1:a ≤ sup := by
                        apply hsup.left at hs
                        exact hs
                    exact h1
                ·   have h2:sup ≤ b := by
                        apply hsup.right
                        unfold upperBounds
                        intro x hx
                        exact hx.left.right
                    exact h2

            have fcontsup := cont_f sup_in_ab
            have eps':ε/|f a| > 0:= by exact div_pos ε_pos abs_fa_pos
            rcases fcontsup (ε / |f a|) eps' with ⟨δ, δ_pos, Hδ⟩
            use δ

            constructor
            ·   exact δ_pos
            ·   intro y hy y_cerca
                have y_in_ab : y ∈ Set.Icc a b := hy.left
            -- aquí introducimos H , introducir en Hδ todo lo que tenemos para dejar el valor absoluto |f sup -f y| y jugar sólo con eso
                have H:= Hδ y y_in_ab y_cerca
                simp
                calc
                    |f sup*f a-f y*f a| = |f a*(f sup- f y)| := by ring_nf
                    _=|f a| * |f sup - f y| := by rw[abs_mul]
                exact (lt_div_iff₀' abs_fa_pos).mp H

        rw[Continuous_at_in] at cont_g
        have ε1_pos: 0 < |f sup * f a| := by
            exact abs_pos_of_neg pos_lt
        specialize cont_g |f sup * f a| ε1_pos
        have cont_g':= cont_g
        obtain ⟨δ,Hδ,hg⟩:=cont_g
        --ahora toca construir el y para especializer en h. para ello usamos prop.del supremo
        have choosey : ∃ y ∈ s, sup-δ < y:= by
            have sup_is_IsLUB: IsLUB s sup:= by
                constructor
                · exact hsup.left
                · exact hsup.right
            have sup_is_sup: sSup s = sup:=by
                exact IsLUB.csSup_eq hsup Nonempty_s
            rw [←sup_is_sup]
            have y_men_delta_lt_sup: sSup s-δ/2 ≤ sSup s := by linarith
            obtain minor_then_diff := (Real.le_sSup_iff BddAboved_s Nonempty_s).mp y_men_delta_lt_sup
            have Hδ1:-δ/2<0:=by linarith
            specialize minor_then_diff (-δ/2)
            obtain ⟨x, hx_in, hx_gt⟩ := minor_then_diff Hδ1
            use x
            constructor
            · exact hx_in
            · linarith

        obtain ⟨y,hy1,hy2⟩:= choosey
        have abs_lt_delta: |sup - y|<δ:= by
            have y_less_sup: y≤sup :=by exact hsup.left hy1
            have hipo:= abs_sub_less sup y δ Hδ y_less_sup
            exact hipo hy2

        specialize hg y
        have hg':= hg hy1 abs_lt_delta
        have hy11 : f y * f a > 0 := hy1.right
        have fyfa_abs_sub_neg_ne_lt: |f sup * f a - f y * f a| ≥ |f sup * f a|:= by
            exact abs_sub_neg_pos_le_abs (f sup * f a)  (f y * f a) pos_lt hy11

        linarith
    ·   exfalso







/-
        obtain ⟨y,hy1,hy2,hy3⟩:= choosey
        have fyfa_ht_0:  0 < f y * f a  := by
            rcases hy1 with ⟨_,fyfa_ht_0⟩
            exact fyfa_ht_0

        exact lt_asymm fyfa_ht_0 hy3
-/






-- Probamos que ε' > 0
    cases' pos1_aux with pos_eq pos_gt
    · sorry
    · exfalso
      sorry
