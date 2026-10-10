import Holant.Proofs.Hardness.GeneralEORootNormRigidity
import Holant.Proofs.Hardness.GeneralEOPinnedDescentLabels

/-! Three actual caps suffice: a native loop, one original-family binary,
and its boundary reversal. Their nonzero multipliers are retained. Equal
opposite norms for all actual binaries then force ARS on every central graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
namespace L
export GeneralEORootNormLocal (NormSymmetry mass ars_norm ars_of_related norm_eq_of_mass_eq
  mass_eq_of_norm_eq rootMerge Related)
end L
namespace T
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote)
end T
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels reboundary_denote)
end R
namespace O
export GeneralEOPinnedDescentOperations (word word_weight cap cap_denote)
end O
namespace C
export GeneralEOPinnedDescentLabels (capLabels cap_exact cap_native)
end C
namespace D
export GeneralEOPhaseExtractionDistance (loop labels exact native central)
end D
namespace F
export SelfDualPinObstruction (flip)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def phases (p q : ℂ) : Fin 3 → ℂ := ![1,p/q,q/p]

theorem phases_distinct (p q : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) (hne : p^2 ≠ q^2) :
    Function.Injective (phases p q) := by
  have h1 : p/q ≠ 1 := by
    intro h
    exact hne (congrArg (fun z : ℂ => z^2) ((div_eq_one_iff_eq hq).mp h))
  have h2 : q/p ≠ 1 := by
    intro h
    exact hne (congrArg (fun z : ℂ => z^2) ((div_eq_one_iff_eq hp).mp h).symm)
  have h3 : p/q ≠ q/p := by
    intro h
    apply hne
    simpa only [pow_two] using (div_eq_div_iff hq hp).mp h
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [phases]

theorem phases_unit (p q : ℂ) (_hp : p ≠ 0) (hq : q ≠ 0) (hn : ‖p‖ = ‖q‖) :
    ∀ i, ‖phases p q i‖ = 1 := by
  intro i
  fin_cases i <;> simp [phases,hn,norm_ne_zero_iff.mpr hq]

theorem norm_of_scaled_ars {n : ℕ} (f g : Signature ℂ n) (c : ℂ) (hc : c ≠ 0)
    (equation : g = fun x => c*f x) (hg : GeneralEOARSBoundary.ARSUpToScale g) :
    L.NormSymmetry f := by
  intro x
  have hh := GeneralEOARSBoundary.opposite_norm g hg x
  rw [equation] at hh
  simp only [norm_mul] at hh
  exact L.mass_eq_of_norm_eq (mul_left_cancel₀ (norm_ne_zero_iff.mpr hc) hh)

def reverse (B : Network ℂ 2) : Network ℂ 2 := R.reboundary B (Equiv.swap 0 1)

theorem reverse_value (B : Network ℂ 2) (u v : Bool) :
    (reverse B).denote ![u,v] = B.denote ![v,u] := by
  rw [reverse,R.reboundary_denote]
  change B.denote _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem cap_central {n : ℕ} (B : Network ℂ 2) (U : Network ℂ (n+2))
    (hB : Signature.CentralSupport B.denote) (hU : Signature.CentralSupport U.denote) :
    Signature.CentralSupport (O.cap B U).denote := by
  intro x hx
  have h00 := hB (![false,false]) (by decide)
  have h11 := hB (![true,true]) (by decide)
  have h01 : U.denote (O.word false true x) = 0 := hU _ (by
    rw [O.word_weight]
    simp only [Bool.false_eq_true,ite_false,ite_true]
    omega)
  have h10 : U.denote (O.word true false x) = 0 := hU _ (by
    rw [O.word_weight]
    simp only [Bool.false_eq_true,ite_false,ite_true]
    omega)
  rw [O.cap_denote,h00,h11,h01,h10]
  ring

theorem cap_value {n : ℕ} (B : Network ℂ 2) (U : Network ℂ (n+2))
    (hB : Signature.CentralSupport B.denote) (hq : B.denote ![true,false] ≠ 0)
    (e : Equiv.Perm (Fin (n+2))) :
    (O.cap B (R.reboundary U e)).denote = fun x =>
      B.denote ![true,false] * L.rootMerge U.denote e
        (B.denote ![false,true]/B.denote ![true,false]) x := by
  funext x
  rw [O.cap_denote,R.reboundary_denote]
  rw [hB (![false,false]) (by decide),hB (![true,true]) (by decide)]
  simp only [zero_mul,zero_add,add_zero,Tensor.reindex_apply,L.rootMerge,Function.comp_def]
  field_simp
  ring

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature ℂ (a i.val))

def BinaryNorms : Prop := ∀ (B : Network ℂ 2) (BL : Labelling B.shape s 1 a),
  LabelledNetwork.Exact G B BL → (∀ e, B.edge e = Signature.disequality) →
  Signature.CentralSupport B.denote → ‖B.denote ![false,true]‖ = ‖B.denote ![true,false]‖

variable (B : Network ℂ 2) (BL : Labelling B.shape s 1 a)
variable (hBL : LabelledNetwork.Exact G B BL) (hBN : ∀ e, B.edge e = Signature.disequality)
variable (hBE : Signature.CentralSupport B.denote)
variable (hp : B.denote ![false,true] ≠ 0) (hq : B.denote ![true,false] ≠ 0)
variable (hne : B.denote ![false,true]^2 ≠ B.denote ![true,false]^2)

include hBL hBN hBE hp hq hne in
theorem ars_with_binary (hBinary : BinaryNorms G) (n : ℕ) :
    ∀ (U : Network ℂ n) (UL : Labelling U.shape s 1 a),
      LabelledNetwork.Exact G U UL → (∀ e, U.edge e = Signature.disequality) →
      Signature.CentralSupport U.denote → GeneralEOARSBoundary.ARSUpToScale U.denote := by
  let p := B.denote ![false,true]
  let q := B.denote ![true,false]
  have hd := phases_distinct p q hp hq hne
  have hu := phases_unit p q hp hq (hBinary B BL hBL hBN hBE)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U UL hL hN hE
    by_cases hn0 : n = 0
    · subst n
      have hf (x : Fin 0 → Bool) : F.flip x = x := by funext i; exact Fin.elim0 i
      apply L.ars_of_related U.denote (fun x => by rw [hf])
      intro x y
      have hxy : x = y := Subsingleton.elim x y
      simp only [L.Related,hxy,hf]
      ring
    by_cases hn1 : n = 1
    · subst n
      have hz : ∀ x, U.denote x = 0 := fun x => hE x (by omega)
      apply L.ars_of_related U.denote (fun x => by rw [hz,hz])
      intro x y
      simp only [L.Related,hz,star_zero,mul_zero]
    by_cases hn2 : n = 2
    · subst n
      exact GeneralEOBinaryARS.ars_of_equal_norm U.denote hE (hBinary U UL hL hN hE)
    obtain ⟨k,rfl⟩ : ∃ k, n = k+3 := ⟨n-3,by omega⟩
    have plus (e : Equiv.Perm (Fin (k+3))) :
        GeneralEOARSBoundary.ARSUpToScale (T.merge U.denote e) := by
      rw [← T.merge_denote]
      exact ih (k+1) (by omega) _ (D.labels _ (R.reboundaryLabels U UL e))
        (D.exact G _ _ hL) (D.native _ hN)
        (D.central _ (GeneralEOCentralHoleCoordinates.reboundary_central U e.symm hE))
    have child (Q : Network ℂ 2) (QL : Labelling Q.shape s 1 a)
        (hQL : LabelledNetwork.Exact G Q QL) (hQN : ∀ e,Q.edge e = Signature.disequality)
        (hQE : Signature.CentralSupport Q.denote) (e : Equiv.Perm (Fin (k+3))) :
        GeneralEOARSBoundary.ARSUpToScale (O.cap Q (R.reboundary U e)).denote :=
      ih (k+1) (by omega) _ (C.capLabels _ (R.reboundaryLabels U UL e) Q QL)
        (C.cap_exact G (R.reboundary U e) (R.reboundaryLabels U UL e) hL Q QL hQL)
        (C.cap_native (R.reboundary U e) hN Q hQN)
        (cap_central Q _ hQE (GeneralEOCentralHoleCoordinates.reboundary_central U e.symm hE))
    apply GeneralEORootNormRigidity.ars_of_children (phases p q) hd hu U.denote hE plus
    intro e i
    fin_cases i
    · change L.NormSymmetry (L.rootMerge U.denote e 1)
      intro x
      simpa only [L.rootMerge,T.merge,one_mul] using L.ars_norm _ (plus e) x
    · exact norm_of_scaled_ars _ _ q hq (cap_value B U hBE hq e)
        (child B BL hBL hBN hBE e)
    · let Q := reverse B
      let QL := R.reboundaryLabels B BL (Equiv.swap 0 1)
      have hQE : Signature.CentralSupport Q.denote :=
        GeneralEOCentralHoleCoordinates.reboundary_central B (Equiv.swap 0 1).symm hBE
      have hQq : Q.denote ![true,false] ≠ 0 := by simpa [Q,reverse_value] using hp
      have he := cap_value Q U hQE hQq e
      simp only [Q,reverse_value] at he
      exact norm_of_scaled_ars _ _ p hp he (child Q QL hBL hBN hQE e)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormNetwork
