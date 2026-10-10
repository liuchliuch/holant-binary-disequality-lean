import Holant.Proofs.Reductions.GeneralExtraction.CarrierNormalization
import Holant.Complexity.BinaryInterpolation.Chains.DirectMacro
import Holant.Tractable.Downward


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralPowerExposure
open Holant.Tractable
open NamedContraction GeneralCarrierExistence
open Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation.Chains
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

variable {K : Type*} [Field K] {m n s : ℕ} {arity : ℕ → ℕ}

theorem ordinary_power (F : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (hF : MixedSupport F) (f : Signature K m) (g : Signature K n)
    (hn : 0 < n) (hg : g ≠ 0) (hfg : (⟨m + n, Signature.tensor f g⟩ : AnySignature K) ∈ F) :
    ∃ r : ℕ, 0 < r ∧ ∃ c : K, c ≠ 0 ∧ ∃ N : Network K (r * m),
      NamedContraction.Uses N F ∧ NamedContraction.Native N ∧ N.denote = fun x => c * Carrier.blockPower f r x := by
  obtain ⟨W⟩ := factor_carrier F htwo hF hn g hg
  let N := (Carrier.extracted (CarrierNormalization.arity W)
    (CarrierNormalization.wiring (m := m) W) (CarrierNormalization.background W)
    f g (fun _ => Signature.disequality)).toNetwork
  refine ⟨CarrierNormalization.count W, CarrierNormalization.count_positive W,
    W.graph.denote Fin.elim0, W.nonzero, N, ?_, ?_, ?_⟩
  · intro v
    change (⟨_, (Carrier.extracted (CarrierNormalization.arity W)
      (CarrierNormalization.wiring W) (CarrierNormalization.background W)
      f g (fun _ => Signature.disequality)).vertex
        ((Fintype.equivFin (Carrier.NewVertex (CarrierNormalization.Background W) 0
          (CarrierNormalization.count W))).symm v)⟩ : AnySignature K) ∈ F
    cases (Fintype.equivFin (Carrier.NewVertex (CarrierNormalization.Background W) 0
      (CarrierNormalization.count W))).symm v with
    | inl v => exact CarrierNormalization.background_mem W v
    | inr v => exact hfg
  · intro e
    rfl
  · funext x
    exact CarrierNormalization.extracted_value W f x

structure PowerMacro (G : (i : Fin s) → Signature K (arity i.val)) (f : Signature K m) where
  exponent : ℕ
  positive : 0 < exponent
  scale : K
  scale_ne_zero : scale ≠ 0
  network : Network K (exponent * m)
  labels : Labelling network.shape s 1 arity
  value : (labels.template.network labels.wellFormed G (fun _ => Signature.disequality)).denote =
    fun x => scale * Carrier.blockPower f exponent x

theorem labelled_power (G : (i : Fin s) → Signature K (arity i.val))
    (htwo : (2 : K) ≠ 0)
    (hF : MixedSupport (Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature K))))
    (f : Signature K m) (g : Signature K n) (hn : 0 < n) (hg : g ≠ 0)
    (hfg : (⟨m + n, Signature.tensor f g⟩ : AnySignature K) ∈
      Set.range (fun i => (⟨arity i.val, G i⟩ : AnySignature K))) :
    Nonempty (PowerMacro G f) := by
  obtain ⟨r, hr, c, hc, N, hU, hN, hv⟩ := ordinary_power _ htwo hF f g hn hg hfg
  let L := labellingOfUses arity G N hU (0 : Fin 1)
  refine ⟨⟨r, hr, c, hc, N, L, ?_⟩⟩
  exact (labellingOfUses_denote arity G N hU hN (0 : Fin 1)
    (fun _ => Signature.disequality) rfl).trans hv

/-- Source 2.16's retained-family hypothesis supplies both signs in the
original K coordinates, with no change to the common-one-sided exception. -/
theorem mixedSupport_of_source {F : SignatureFamily AlgebraicComplex}
    (hs : ¬ Holant.Tractable.CommonOneSided F) : MixedSupport F := by
  have H := (Holant.Tractable.commonOneSided_or_bothChargeSigns F).resolve_left hs
  intro b
  cases b with
  | false =>
    obtain ⟨⟨n, f⟩, hf, x, hx, hc⟩ := H.1
    exact ⟨n, f, hf, x, hx, by rw [balance_false]; omega⟩
  | true =>
    obtain ⟨⟨n, f⟩, hf, x, hx, hc⟩ := H.2
    exact ⟨n, f, hf, x, hx, by rwa [balance_true]⟩

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralPowerExposure
