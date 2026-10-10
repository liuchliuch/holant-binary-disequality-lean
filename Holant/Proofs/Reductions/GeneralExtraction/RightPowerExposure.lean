import Holant.Proofs.Reductions.GeneralExtraction.GeneralPowerExposure


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.RightPowerExposure
open NamedContraction GeneralCarrierExistence GeneralPowerExposure
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation.Chains
variable {K O E : Type*} [Field K] {m n p r : ℕ}

def blockSwap (m n : ℕ) : Fin (m+n) ≃ Fin (n+m) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv)

theorem tensor_swap (f : Signature K m) (g : Signature K n) (x : Fin (n+m) → Bool) :
    Signature.tensor f g (fun i => x (blockSwap m n i)) = Signature.tensor g f x := by
  simp [Signature.tensor_apply, blockSwap, mul_comm]

def localOrder (a : O → ℕ) (v : Carrier.NewVertex O p r) :
    Fin (Carrier.newArity a m n v) ≃ Fin (Carrier.newArity a n m v) :=
  match v with
  | .inl _ => Equiv.refl _
  | .inr _ => blockSwap m n

def portOrder (a : O → ℕ) : Carrier.NewPort a m n p r ≃ Carrier.NewPort a n m p r :=
  Equiv.sigmaCongr (Equiv.refl _) (localOrder a)

def extracted (a : O → ℕ) (W : Carrier.Wiring a n m p r E)
    (background : (o : O) → Signature K (a o)) (f : Signature K m) (g : Signature K n)
    (edge : E → Bool → Bool → K) : FiniteNetwork K (Carrier.NewVertex O p r) E (r*n) where
  arity := Carrier.newArity a m n
  ports := (portOrder a).trans (Carrier.extracted a W background g f edge).ports
  vertex := fun v => match v with
    | .inl o => background o
    | .inr _ => Signature.tensor f g
  edge := edge

theorem extracted_denote [Fintype O] [Fintype E]
    (a : O → ℕ) (W : Carrier.Wiring a n m p r E)
    (background : (o : O) → Signature K (a o)) (f : Signature K m) (g : Signature K n)
    (edge : E → Bool → Bool → K) (x : Fin (r*n) → Bool) :
    (extracted a W background f g edge).denote x =
      (Carrier.extracted a W background g f edge).denote x := by
  unfold FiniteNetwork.denote
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    cases v with
    | inl o => rfl
    | inr v =>
      exact tensor_swap f g
        (fun i => Sum.elim x z ((Carrier.extracted a W background g f edge).ports ⟨.inr v,i⟩))
  · rfl

theorem ordinary_power (F : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (hF : MixedSupport F) (f : Signature K m) (g : Signature K n)
    (hm : 0 < m) (hf : f ≠ 0) (hfg : (⟨m+n, Signature.tensor f g⟩ : AnySignature K) ∈ F) :
    ∃ r : ℕ, 0 < r ∧ ∃ c : K, c ≠ 0 ∧ ∃ N : Network K (r*n),
      NamedContraction.Uses N F ∧ NamedContraction.Native N ∧ N.denote = fun x => c * Carrier.blockPower g r x := by
  obtain ⟨W⟩ := factor_carrier F htwo hF hm f hf
  let N := (extracted (CarrierNormalization.arity W) (CarrierNormalization.wiring (m:=n) W)
    (CarrierNormalization.background W) f g (fun _ => Signature.disequality)).toNetwork
  refine ⟨CarrierNormalization.count W, CarrierNormalization.count_positive W,
    W.graph.denote Fin.elim0, W.nonzero, N, ?_, ?_, ?_⟩
  · intro v
    change (⟨_, (extracted (CarrierNormalization.arity W) (CarrierNormalization.wiring W)
      (CarrierNormalization.background W) f g (fun _ => Signature.disequality)).vertex
        ((Fintype.equivFin (Carrier.NewVertex (CarrierNormalization.Background W) 0
          (CarrierNormalization.count W))).symm v)⟩ : AnySignature K) ∈ F
    cases (Fintype.equivFin (Carrier.NewVertex (CarrierNormalization.Background W) 0
      (CarrierNormalization.count W))).symm v with
    | inl v => exact CarrierNormalization.background_mem W v
    | inr v => exact hfg
  · intro e
    rfl
  · funext x
    rw [FiniteNetwork.denote_toNetwork, extracted_denote]
    simpa only [FiniteNetwork.denote_toNetwork] using CarrierNormalization.extracted_value W g x

theorem labelled_power {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) (htwo : (2 : K) ≠ 0)
    (hF : MixedSupport (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature K))))
    (f : Signature K m) (g : Signature K n) (hm : 0 < m) (hf : f ≠ 0)
    (hfg : (⟨m+n, Signature.tensor f g⟩ : AnySignature K) ∈
      Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature K))) : Nonempty (PowerMacro G g) := by
  obtain ⟨r, hr, c, hc, N, hU, hN, hv⟩ := ordinary_power _ htwo hF f g hm hf hfg
  let L := labellingOfUses arity G N hU (0 : Fin 1)
  exact ⟨⟨r, hr, c, hc, N, L,
    (labellingOfUses_denote arity G N hU hN (0 : Fin 1) (fun _ => Signature.disequality) rfl).trans hv⟩⟩

end Holant.LocalDrafts.Hardness.GeneralExtraction.RightPowerExposure
