import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralGoldenSix

/-! Generic I/opposite-I coefficient proof extracted from RankThree/GoldenKeys.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
open Holant.Certificates Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralPreservers
open scoped BigOperators

abbrev RawProjection := Fin 3 → GoldenInt
abbrev RationalGolden := ℚ × ℚ

def conjugateGolden (v : GoldenInt) : GoldenInt := ⟨v.a+v.b,-v.b⟩

theorem conjugateGolden_eval (v : GoldenInt) :
    GoldenInt.eval (conjugateGolden v) = v.a+v.b*(1-goldenRatio) := by
  simp [conjugateGolden,GoldenInt.eval]
  ring

theorem norm_ne_zero {v : GoldenInt} (hv : v ≠ GoldenInt.zero) :
    GoldenInt.norm v ≠ 0 := by
  intro hn
  have hprod := GoldenInt.norm_identity v
  rw [hn,Int.cast_zero] at hprod
  rcases mul_eq_zero.mp hprod.symm with h | h
  · exact hv ((golden_eval_zero_iff v).mp h)
  · have he : GoldenInt.eval (conjugateGolden v) = 0 := by
      rw [conjugateGolden_eval]
      exact h
    have hz := (golden_eval_zero_iff _).mp he
    have hb := congrArg GoldenInt.b hz
    have ha := congrArg GoldenInt.a hz
    apply hv
    cases v
    simp_all [conjugateGolden,GoldenInt.zero]

def ratioKey (u v : GoldenInt) : RationalGolden :=
  let w := GoldenInt.mul u (conjugateGolden v)
  ((w.a : ℚ)/(GoldenInt.norm v : ℚ),(w.b : ℚ)/(GoldenInt.norm v : ℚ))

noncomputable def rationalEval (p : RationalGolden) : ℝ :=
  (p.1 : ℝ)+(p.2 : ℝ)*goldenRatio

theorem rationalEval_injective : Function.Injective rationalEval := by
  intro p q h
  have hb : p.2 = q.2 := by
    by_contra hn
    have hd : (p.2 : ℝ)-(q.2 : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hn
    have hirr : Irrational goldenRatio := Real.goldenRatio_irrational
    apply (hirr.ne_rat ((q.1-p.1)/(p.2-q.2)))
    push_cast
    apply (eq_div_iff hd).mpr
    dsimp [rationalEval] at h
    linarith
  have ha : p.1 = q.1 := by
    dsimp [rationalEval] at h
    rw [hb] at h
    exact_mod_cast (add_right_cancel h)
  exact Prod.ext ha hb

theorem ratioKey_eval (u v : GoldenInt) (hv : v ≠ GoldenInt.zero) :
    rationalEval (ratioKey u v) = GoldenInt.eval u / GoldenInt.eval v := by
  have hnv : (GoldenInt.norm v : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (norm_ne_zero hv)
  have hev : GoldenInt.eval v ≠ 0 := GoldenInt.eval_ne_zero _ (norm_ne_zero hv)
  have hp : (GoldenInt.norm v : ℝ) =
      GoldenInt.eval v * GoldenInt.eval (conjugateGolden v) := by
    rw [conjugateGolden_eval]
    exact GoldenInt.norm_identity v
  have hconj : GoldenInt.eval (conjugateGolden v) ≠ 0 := by
    intro h
    apply hnv
    rw [hp,h,mul_zero]
  calc
    rationalEval (ratioKey u v) =
        GoldenInt.eval (GoldenInt.mul u (conjugateGolden v))/(GoldenInt.norm v : ℝ) := by
      unfold rationalEval ratioKey
      push_cast
      dsimp [GoldenInt.eval]
      ring
    _ = (GoldenInt.eval u*GoldenInt.eval (conjugateGolden v))/
        (GoldenInt.eval v*GoldenInt.eval (conjugateGolden v)) := by rw [GoldenInt.eval_mul,hp]
    _ = GoldenInt.eval u/GoldenInt.eval v := by field_simp [hev,hconj] <;> ring

@[ext] structure ProjectionKey where
  pivot : Fin 3
  entries : Fin 3 → RationalGolden
  deriving DecidableEq

def projectionKey (v : RawProjection) : Option ProjectionKey :=
  if v 0 ≠ GoldenInt.zero then some ⟨0,fun j => ratioKey (v j) (v 0)⟩
  else if v 1 ≠ GoldenInt.zero then some ⟨1,fun j => ratioKey (v j) (v 1)⟩
  else if v 2 ≠ GoldenInt.zero then some ⟨2,fun j => ratioKey (v j) (v 2)⟩
  else none

theorem projectionKey_parts {v : RawProjection} {k : ProjectionKey}
    (hk : projectionKey v = some k) :
    v k.pivot ≠ GoldenInt.zero ∧
    (∀ i : Fin 3, i < k.pivot → v i = GoldenInt.zero) ∧
    (∀ i : Fin 3, rationalEval (k.entries i) =
      GoldenInt.eval (v i)/GoldenInt.eval (v k.pivot)) := by
  unfold projectionKey at hk
  split_ifs at hk with h0 h1 h2
  · cases Option.some.inj hk
    exact ⟨h0,by intro i hi; change i<(0 : Fin 3) at hi; omega,
      fun i => ratioKey_eval _ _ h0⟩
  · cases Option.some.inj hk
    refine ⟨h1,?_,fun i => ratioKey_eval _ _ h1⟩
    intro i hi
    change i<(1 : Fin 3) at hi
    have : i=0 := Fin.ext (by omega)
    subst i
    exact not_ne_iff.mp h0
  · cases Option.some.inj hk
    refine ⟨h2,?_,fun i => ratioKey_eval _ _ h2⟩
    intro i hi
    change i<(2 : Fin 3) at hi
    have : i=0 ∨ i=1 := by omega
    rcases this with rfl | rfl
    · exact not_ne_iff.mp h0
    · exact not_ne_iff.mp h1

def projectionCross (u v : RawProjection) (a b : Fin 3) : GoldenInt :=
  GoldenInt.sub (GoldenInt.mul (u a) (v b)) (GoldenInt.mul (u b) (v a))

theorem projectionCross_eval (u v : RawProjection) (a b : Fin 3) :
    GoldenInt.eval (projectionCross u v a b) =
      GoldenInt.eval (u a)*GoldenInt.eval (v b)-
        GoldenInt.eval (u b)*GoldenInt.eval (v a) := by
  simp [projectionCross]

/-- Distinct nonzero rational keys supply a genuine nonzero GoldenInt cross.
This is why the finite key count really counts quotient directions. -/
theorem distinct_keys_cross {u v : RawProjection} {k l : ProjectionKey}
    (hu : projectionKey u = some k) (hv : projectionKey v = some l) (hkl : k ≠ l) :
    ∃ a b : Fin 3, GoldenInt.norm (projectionCross u v a b) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hz (a b : Fin 3) : projectionCross u v a b = GoldenInt.zero := by
    by_contra h
    exact norm_ne_zero h (hn a b)
  have he (a b : Fin 3) : GoldenInt.eval (u a)*GoldenInt.eval (v b) =
      GoldenInt.eval (u b)*GoldenInt.eval (v a) := by
    have h := congrArg GoldenInt.eval (hz a b)
    rw [projectionCross_eval,GoldenInt.eval_zero] at h
    exact sub_eq_zero.mp h
  obtain ⟨huk,huz,hue⟩ := projectionKey_parts hu
  obtain ⟨hvl,hvz,hve⟩ := projectionKey_parts hv
  have huk' : GoldenInt.eval (u k.pivot) ≠ 0 := GoldenInt.eval_ne_zero _ (norm_ne_zero huk)
  have hvl' : GoldenInt.eval (v l.pivot) ≠ 0 := GoldenInt.eval_ne_zero _ (norm_ne_zero hvl)
  have hp : k.pivot=l.pivot := by
    rcases lt_trichotomy k.pivot l.pivot with h | h | h
    · have hh := he k.pivot l.pivot
      rw [hvz _ h,GoldenInt.eval_zero,mul_zero] at hh
      exact False.elim ((mul_ne_zero huk' hvl') hh)
    · exact h
    · have hh := he k.pivot l.pivot
      rw [huz _ h,GoldenInt.eval_zero,zero_mul] at hh
      exact False.elim ((mul_ne_zero huk' hvl') hh)
  have hvk' : GoldenInt.eval (v k.pivot) ≠ 0 := by simpa only [hp] using hvl'
  apply hkl
  apply ProjectionKey.ext hp
  funext i
  apply rationalEval_injective
  rw [hue i,hve i,←hp]
  apply (div_eq_div_iff huk' hvk').mpr
  simpa only [mul_comm] using (he k.pivot i).symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
