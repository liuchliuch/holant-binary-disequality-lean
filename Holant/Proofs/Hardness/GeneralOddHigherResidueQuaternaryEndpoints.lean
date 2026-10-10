import Holant.Proofs.Hardness.GeneralOddResidueSource

/-! The nonprimitive two-sided residue supplies both orientations of a minimal
endpoint graph. A positive charge q = (t+1)d is balanced with t copies of the
existing opposite terminal, then reduced by actual noncancelling X cuts to
charge d. Every output vertex and edge belongs to the original ordinary
family after the exact inverse chart transform. This closes the missing
opposite-endpoint existence step; it does not yet assert a pin or DEQ4 macro. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryEndpoints
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps NativeCopies
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource
namespace M
export GeneralOddMinimalTerminal (Minimal endpoint supported_endpoint noCuts controlled actual)
end M
namespace Structure
export Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure
  (twoConstants ordinary_terminal_decomposition)
end Structure
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (D : M.Minimal G)

/-- A finite number of actual copies reduces a positive multiple to exactly
one lattice unit. Neither inverse copies nor a desired output table is used. -/
theorem opposite_endpoint (hs : ¬CommonOneSided (kCoordinates (original G)))
    (b : Bool) (hb : M.endpoint G D (!b)≠0) :
    ∃ k : Fin s,∃ t : ℕ,∃ E : M.Minimal G,
      E.arity=D.arity ∧ M.endpoint G E b≠0 ∧
      E.graph.shape.vertices=1+t*D.graph.shape.vertices ∧
      D.arity+2*E.graph.shape.edges=a k.val+t*(D.arity+2*D.graph.shape.edges) := by
  obtain ⟨k,x,hx,hpos⟩ := GeneralOddResidueMinimal.positive_original G hs b
  let q := (balance b x).toNat
  have hq : (q : ℤ)=balance b x := Int.toNat_of_nonneg (le_of_lt hpos)
  have hd : 0<D.arity := by obtain ⟨m,hm⟩ := D.odd; omega
  obtain ⟨l,hl⟩ := GeneralOddMinimalTerminal.opposite_divisible G D b hb k x q hx
    (by omega) hq.symm
  have hlpos : 0<l := by
    by_contra h
    have hl0 : l=0 := by omega
    have hq0 : q=0 := by simpa [hl0] using hl
    omega
  let t := l-1
  have hl' : l=t+1 := by dsimp [t]; omega
  have he : q=t*D.arity+D.arity := by rw [hl,hl']; ring
  let P := toNative (Network.corolla (G k))
  let H := toNative D.graph
  let N := P.tensor (copies H t)
  let w := appendWord x (copyWord (fun _ : Fin D.arity => !b) t)
  have hPF : Uses P (kCoordinates (original G)) :=
    toNative_uses (original G) _ (fun _ => ⟨k,rfl⟩)
  have hPX : Native P := toNative_native _ (fun e => Fin.elim0 e)
  have hHF : Uses H (kCoordinates (original G)) := toNative_uses (original G) _ D.uses
  have hHX : Native H := toNative_native _ D.ordinary
  have hNF : Uses N (kCoordinates (original G)) :=
    tensor_uses _ _ _ hPF (copies_uses _ H hHF t)
  have hNX : Native N := tensor_native _ _ hPX (copies_native H hHX t)
  have hpx : P.denote x≠0 := by simpa [P,toNative_denote] using hx
  have hhy : H.denote (fun _ => !b)≠0 := by simpa [H,toNative_denote,M.endpoint] using hb
  have hw : N.denote w≠0 := by
    change (P.tensor (copies H t)).denote (appendWord x (copyWord (fun _ => !b) t))≠0
    rw [tensor_word,copies_word]
    exact mul_ne_zero hpx (pow_ne_zero t hhy)
  have hc : balance b w=D.arity := by
    simp only [w,balance_append,balance_copy,←hq]
    have hc : balance b (fun _ : Fin D.arity => !b)=-(D.arity : ℤ) := by
      cases b <;> simp [balance]
    rw [hc]
    have he' : (q : ℤ)=(t : ℤ)*D.arity+D.arity := by exact_mod_cast he
    linarith
  obtain ⟨U,hUF,hUX,hUb,hUv,hUe⟩ := GeneralOddHighTerminalGcd.positive_charge
    (kCoordinates (original G)) (by norm_num) b N hNF hNX w hw D.arity hd hc
  have hdiag : sourceKBasis.symm.action (toOrdinary U).denote=U.denote := by
    rw [toOrdinary_denote,InvertibleKernel.symm_action_action]
  have hUnz : (toOrdinary U).denote≠0 := by
    intro hz
    have h := congrArg sourceKBasis.symm.action hz
    rw [hdiag] at h
    exact hUb (congrFun (h.trans (Signature.coordinateAction_zero _)) (fun _ => b))
  let E : M.Minimal G := {
    arity := D.arity
    odd := D.odd
    graph := toOrdinary U
    uses := toOrdinary_uses (original G) U hUF
    ordinary := toOrdinary_ordinary U hUX
    nonzero := hUnz
    minimal := D.minimal }
  refine ⟨k,t,E,rfl,?_,?_,?_⟩
  · change sourceKBasis.symm.action (toOrdinary U).denote (fun _ => b)≠0
    rw [hdiag]
    exact hUb
  · change U.shape.vertices=1+t*D.graph.shape.vertices
    have hPv : P.shape.vertices=1 := rfl
    have hHv : H.shape.vertices=D.graph.shape.vertices := rfl
    simpa only [N,Network.tensor_vertices,copies_vertices,hPv,hHv] using hUv
  · change D.arity+2*U.shape.edges=a k.val+t*(D.arity+2*D.graph.shape.edges)
    simp only [N,Network.tensor_edges,GeneralOddHighTerminalCharge.copies_edges,
      copyArity_eq] at hUe
    have hPe : P.shape.edges=0 := rfl
    have hHe : H.shape.edges=D.graph.shape.edges := rfl
    rw [hPe,hHe] at hUe
    nlinarith [hUe]

/-- Both endpoint orientations are now actual minimal ordinary graphs at the
same arity. Their other endpoint coefficients remain arbitrary and may vanish. -/
theorem both_endpoints (hh : 3≤D.arity)
    (hs : ¬CommonOneSided (kCoordinates (original G))) :
    ∃ L R : M.Minimal G,L.arity=D.arity ∧ R.arity=D.arity ∧
      M.endpoint G L false≠0 ∧ M.endpoint G R true≠0 := by
  obtain ⟨b,hb⟩ := M.supported_endpoint G D hh
  obtain ⟨k,t,E,he,hE,_,_⟩ := opposite_endpoint G D hs b hb
  cases b
  · exact ⟨E,D,he,rfl,hE,hb⟩
  · exact ⟨D,E,rfl,he,hb,hE⟩

/-- Every produced row has the exact two-constant decomposition by minimality,
and its oracle installation is the already proved original G/Eq programme. -/
theorem endpoint_receipt (hh : 3≤D.arity) :
    sourceKBasis.symm.action D.graph.denote=
      Structure.twoConstants (M.endpoint G D false) (M.endpoint G D true) ∧
    Nonempty (GeneralOddHighTerminalAccess.Reduction G (M.actual G D)) :=
  ⟨Structure.ordinary_terminal_decomposition D.graph.denote D.odd hh (M.noCuts G D),
    ⟨M.controlled G D⟩⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryEndpoints
