import Holant.Certificates.TetrahedralDeck.KernelSemantics

/-! The executable Gaussian ancestor is exactly four times the source's
Frobenius reconstruction. The scaling is proved before any certificate is used. -/
namespace Holant.Certificates.TetrahedralDeck
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def complexImages (s : Fin 3) : Fin 4 → FourTensor :=
  ![(1/2 : ℂ) • C,TetrahedralOrientation.axisR (survivor s 0),
    TetrahedralOrientation.axisR (survivor s 1),TetrahedralOrientation.axisR (survivor s 2)]

theorem source_ancestor_eq (s : Fin 3) (x : SixWord) :
    TetrahedralAffine.complexAncestor s x = ∑ k : Fin 4,
      TetrahedralOrientation.dual k (x 0) (x 1)*complexImages s k (fun j => x j.succ.succ) := rfl

theorem embed_gDual (k : Fin 4) (a b : Bool) :
    embed (gDual k a b) = 2*TetrahedralOrientation.dual k a b := by
  fin_cases k <;> cases a <;> cases b <;>
    norm_num [gDual,gSigned,gQ,gzero,gone,gI,gneg,embed,TetrahedralOrientation.dual,
      Q0,Q1,Q2,Q3,Signature.equality,smul_eq_mul] <;> ring

theorem embed_gR (k : Fin 4) (x : Word) :
    embed (gR k x) = 2*TetrahedralOrientation.axisR k x := by
  fin_cases k <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    norm_num [gR,gSigned,gP2,gQ,gzero,gone,gI,gneg,gmul,embed,
      TetrahedralOrientation.axisR,P2,Q0,Q1,Q2,Q3,Signature.equality,smul_eq_mul,h0,h1,h2,h3] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem embed_gImages (s : Fin 3) (k : Fin 4) (x : Word) :
    embed (gImages s k x) = 2*complexImages s k x := by
  fin_cases k
  · simp [gImages,complexImages,gP2,embed_mul,embed_gQ,quaternionBasis,C,P2,smul_eq_mul]
  · exact embed_gR _ _
  · exact embed_gR _ _
  · exact embed_gR _ _

theorem embed_gAncestor (s : Fin 3) (x : SixWord) :
    embed (gAncestor s x) = 4*TetrahedralAffine.complexAncestor s x := by
  simp [gAncestor,gsum4,embed_add,embed_mul,embed_gDual,embed_gImages,
    source_ancestor_eq,Fin.sum_univ_succ]
  ring

end
end Holant.Certificates.TetrahedralDeck
