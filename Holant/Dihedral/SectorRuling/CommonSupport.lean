import Holant.Dihedral.SectorRuling.MatchingSupport

/-! Full source sampled matching hypothesis implies a common actual support
and therefore one original perfect matching, including its support parity. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Certificates Holant.Dihedral.EndpointParallelogram
open Holant.Dihedral.TwoCardLocalization
set_option backward.isDefEq.respectTransparency false

def tensorPencil {n : ℕ} (U V : Signature Scalar n) (t : Scalar) : Signature Scalar n :=
  fun x => U x+t*V x

theorem coefficients_pencil {n : ℕ} (U V : Signature Scalar n) (t : Scalar) :
    coefficients (tensorPencil U V t)=pencil (coefficients U) (coefficients V) t := rfl

theorem coefficients_ne_zero {n : ℕ} (q : Signature Scalar n) (hq : q ≠ 0) : coefficients q ≠ 0 := by
  intro hz
  apply hq
  funext x
  have h := congrFun hz (bitsEquiv (Fin n) x)
  simpa [coefficients] using h

/-- No common support or ruling is among the hypotheses. All m phases are
used; the m=3 obstruction is the proved literal -mu_3 coefficient ratio. -/
theorem source_common_support {m s : ℕ} (hm : 3 ≤ m) (U V : Signature Scalar (2*s))
    (hs : ∀ t : Scalar,Roots m t → tensorPencil U V t=0 ∨ MatchingSample m s (tensorPencil U V t))
    (a b : Scalar) (ha : Roots m a) (hb : Roots m b)
    (hna : tensorPencil U V a ≠ 0) (hnb : tensorPencil U V b ≠ 0) :
    support (coefficients (tensorPencil U V a))=support (coefficients (tensorPencil U V b)) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨i,hi⟩ := gridValue_surjective a ha
  obtain ⟨j,hj⟩ := gridValue_surjective b hb
  have hsample (k : Grid m) : pencil (coefficients U) (coefficients V) (gridValue k)=0 ∨
      SampleInfo m (2^s) (pencil (coefficients U) (coefficients V) (gridValue k)) := by
    rcases hs (gridValue k) (gridValue_roots k) with hk|hk
    · left
      rw [←coefficients_pencil,hk]
      rfl
    · right
      exact matching_sample_info (by omega) _ hk
  have hn₀ : pencil (coefficients U) (coefficients V) (gridValue i) ≠ 0 := by
    rw [hi,←coefficients_pencil]
    exact coefficients_ne_zero _ hna
  have hn₁ : pencil (coefficients U) (coefficients V) (gridValue j) ≠ 0 := by
    rw [hj,←coefficients_pencil]
    exact coefficients_ne_zero _ hnb
  have he := finite_pencil_support hm (by positivity : 0<2^s) gridValue gridValue_injective
    (grid_card m) (coefficients U) (coefficients V) hsample i j hn₀ hn₁
  simpa only [hi,hj,coefficients_pencil] using he

/-- Equal actual monomial supports determine the same literal original mate
function, even when the coefficient tables and their scales differ. -/
theorem matching_of_support_eq {n r s : ℕ}
    (p₀ : (Fin r × Bool) ≃ Fin n) (p₁ : (Fin s × Bool) ≃ Fin n)
    (A₀ : Fin r → Mat) (A₁ : Fin s → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,IsMonomial (A₀ e)) (hA₁ : ∀ e,IsMonomial (A₁ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0)
    (hs : support (coefficients (MatchingContractionClosure.productValue p₀ A₀ κ₀))=
      support (coefficients (MatchingContractionClosure.productValue p₁ A₁ κ₁))) :
    Pairing.ofPorts p₀=Pairing.ofPorts p₁ := by
  obtain ⟨a,ha⟩ := product_cardMatching p₀ A₀ κ₀ hA₀ hκ₀
  obtain ⟨b,hb⟩ := product_cardMatching p₁ A₁ κ₁ hA₁ hκ₁
  apply Pairing.code_injective
  apply coset_direction_unique _ _ a b
  ext x
  have he := Finset.ext_iff.mp hs x
  simp only [mem_support,coefficients] at he
  exact (ha x).symm.trans (he.trans (hb x))

end Holant.Dihedral.SectorRuling
