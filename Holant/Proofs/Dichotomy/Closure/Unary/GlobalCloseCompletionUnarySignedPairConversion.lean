import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnarySignedPairGraph

/-! Every actual nonsingular signed paired quaternary with both actual pins
produces an actual unsigned paired quaternary. The exceptional entrywise
square is corrected using an internally produced weighted antidiagonal;
there are no physical coordinate-flip assumptions or omitted zero patterns. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnarySignedPairConversion
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain
open OrdinaryNegativeCubicGadgets
namespace A
export GlobalCloseCompletionUnarySignedPairAlgebra
  (row square anti corrected exception_full square_nonsingular corrected_nonsingular)
end A
namespace R
export GlobalCloseCompletionUnarySignedPairGraph
  (squared squared_value bundles transpose_value cap cap_value correct correct_value)
end R
namespace C
export GlobalCloseCompletionPairedSeriesCore (row)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable {H : (j : Fin r)→Signature K (a j.val)}
variable (pins : Bool→Macro H 1) (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (N : Macro H 4) (B : Matrix Bool Bool K) (e₀ e₁ : Bool)
variable (form : N.network.denote=A.row B e₀ e₁) (det : B.det≠0)

include pinsForm form det in
theorem exists_adjacent : ∃V : Macro H 4,∃M : Matrix Bool Bool K,
    M.det≠0 ∧ V.network.denote=A.row M false false := by
  classical
  by_cases easy : B false false*B true true+B false true*B true false≠0
  · exact ⟨R.squared N,A.square B false false,A.square_nonsingular B false false det easy,
      R.squared_value N B e₀ e₁ form⟩
  · have full:=A.exception_full B det (not_not.mp easy)
    cases e₀ with
    | true=>
      let D:=R.cap pins N e₁
      have hd : D.network.denote=A.anti (fun b=>B b false):=R.cap_value pins pinsForm N B e₁ form
      exact ⟨R.correct N D true e₁,A.corrected B (fun b=>B b false) true e₁,
        A.corrected_nonsingular B _ true e₁ det (fun b=>full b false),
        R.correct_value N D B _ true e₁ form hd⟩
    | false=>
      cases e₁ with
      | false=>exact ⟨N,B,det,form⟩
      | true=>
        let D:=R.cap pins (N.reindex R.bundles) false
        have hd : D.network.denote=A.anti (fun b=>B false b) :=
          R.cap_value pins pinsForm (N.reindex R.bundles) B.transpose false
            (R.transpose_value N B false true form)
        exact ⟨R.correct N D false true,A.corrected B (fun b=>B false b) false true,
          A.corrected_nonsingular B _ false true det (fun b=>full false b),
          R.correct_value N D B _ false true form hd⟩

theorem interleaved (V : Macro H 4) (M : Matrix Bool Bool K)
    (form : V.network.denote=A.row M false false) :
    (V.reindex (Equiv.swap 1 2)).network.denote=C.row M := by
  rw [Macro.reindex_denote,form]
  funext x
  cases h0 : x 0 <;>cases h1 : x 1 <;>cases h2 : x 2 <;>cases h3 : x 3 <;>
    simp [Tensor.reindex,A.row,C.row,Equiv.swap_apply_def,h0,h1,h2,h3]

include pinsForm form det in
theorem exists_interleaved : ∃V : Macro H 4,∃M : Matrix Bool Bool K,
    M.det≠0 ∧ V.network.denote=C.row M := by
  obtain ⟨V,M,hm,hv⟩:=exists_adjacent pins pinsForm N B e₀ e₁ form det
  exact ⟨V.reindex (Equiv.swap 1 2),M,hm,interleaved V M hv⟩

structure Output where
  graph : Macro H 4
  matrix : Matrix Bool Bool K
  nonsingular : matrix.det≠0
  form : graph.network.denote=C.row matrix

def produce : Output (H:=H) :=
  let e:=exists_interleaved pins pinsForm N B e₀ e₁ form det
  let V:=Classical.choose e
  let h:=Classical.choose_spec e
  ⟨V,Classical.choose h,(Classical.choose_spec h).1,(Classical.choose_spec h).2⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnarySignedPairConversion
end
