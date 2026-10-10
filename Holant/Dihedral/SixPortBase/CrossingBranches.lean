import Holant.Dihedral.SixPortBase.CrossingOriginal

/-! The P/P and P/C support obstructions from actual coefficients. Every
matching uses the original residual ports, and both sectors share one actual
pair contraction. No support or contraction-cardinality assumptions are inputs. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase.Crossing
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
set_option backward.isDefEq.respectTransparency false

/-- The first pair is the original distinguished physical pair. -/
def sourceRows (U V : Mat) (P Q : PairWord → Residual) : PairWord → Residual :=
  fun w x => U w.1 w.2*P w x+V w.1 w.2*Q w x

def contractSource (c : (Bool × Bool) ≃ Fin 4) (γ : Bool)
    (H : PairWord → Residual) : Rows := fun w => originalContract c γ (H w)

/-- Linearity is proved on the literal four-term coefficient sum. -/
theorem contract_sourceRows (c : (Bool × Bool) ≃ Fin 4) (γ : Bool)
    (U V : Mat) (P Q : PairWord → Residual) :
    contractSource c γ (sourceRows U V P Q)=
      sumRows U V (fun w => originalContract c γ (P w))
        (fun w => originalContract c γ (Q w)) := by
  funext w u v
  simp only [contractSource,sourceRows,originalContract,sumRows,Fintype.sum_bool]
  ring

theorem pp_actual_card {ε : Bool} (U V : Mat)
    (hU : ParitySupported ε U) (hV : ParitySupported (!ε) V)
    (p q : (Fin 2 × Bool) ≃ Fin 4) (A B : Fin 2 → Mat) (κ μ : Scalar)
    (hA : ∀ e,IsMonomial (A e)) (hB : ∀ e,IsMonomial (B e))
    (hκ : κ ≠ 0) (hμ : μ ≠ 0) :
    ∃ c : (Bool × Bool) ≃ Fin 4,Crossed p c ∧ Crossed q c ∧ ∀ γ : Bool,
      (rowSupport (contractSource c γ (sourceRows U V
        (fun _ => productValue p A κ) (fun _ => productValue q B μ)))).card=
          2*((binarySupport U).card+(binarySupport V).card) := by
  obtain ⟨c,hp,hq⟩ := exists_common_crossing_chart p q
  refine ⟨c,hp,hq,?_⟩
  intro γ
  rw [contract_sourceRows]
  exact pp_card U V _ _ hU hV
    (fun _ => original_contract_monomial hp A κ hA hκ γ)
    (fun _ => original_contract_monomial hq B μ hB hμ γ)

/-- A C endpoint may vary with the original p-word. The single fixed
nonsingular factor and the nonzero singleton factor force one output word.
Complementary endpoint axes are a special case of this stronger statement. -/
theorem pc_actual_card_projection {ε : Bool} (U V : Mat)
    (hU : ParitySupported ε U) (hV : ParitySupported (!ε) V) (hVm : IsMonomial V)
    (p q : (Fin 2 × Bool) ≃ Fin 4) (A : Fin 2 → Mat)
    (B : PairWord → Fin 2 → Mat) (κ μ : Scalar)
    (hA : ∀ e,IsMonomial (A e)) (hB : ∀ w,OnePointProduct (B w))
    (hκ : κ ≠ 0) (hμ : μ ≠ 0) :
    ∃ c : (Bool × Bool) ≃ Fin 4,Crossed p c ∧ Crossed q c ∧ ∀ γ : Bool,
      let H := contractSource c γ (sourceRows U V
        (fun _ => productValue p A κ) (fun w => productValue q (B w) μ))
      (rowSupport H).card=2*(binarySupport U).card+2 ∧
      ((rowSupport H).image Prod.fst).card=(binarySupport U).card+2 := by
  obtain ⟨c,hp,hq⟩ := exists_common_crossing_chart p q
  refine ⟨c,hp,hq,?_⟩
  intro γ
  dsimp only
  rw [contract_sourceRows]
  exact ⟨pc_card U V _ _ hU hV hVm
    (fun _ => original_contract_monomial hp A κ hA hκ γ)
    (fun w => original_contract_point hq (B w) μ (hB w) hμ γ),
    pc_projection_card U V _ _ hU hV hVm
    (fun _ => original_contract_monomial hp A κ hA hκ γ)
    (fun w => original_contract_point hq (B w) μ (hB w) hμ γ)⟩

end Holant.Dihedral.SixPortBase.Crossing
