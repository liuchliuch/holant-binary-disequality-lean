import Holant.Proofs.Hardness.GeneralEOPairedFamilyMinorRaw

/-! Every source palette row expands to its literal finite list of parent
factors. Constants and identified variables are compiled within each factor;
tensors of two or more signed original rows require no extra oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleRaw
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding GeneralEOPairedCSPFamilyRaw
namespace M
export GeneralEOPairedFamilyMinorRaw (RowInput rowEncoding port portComputes labelIndexComputes)
end M
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (mapComputes flatten lengthComputes)
end W
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s t : ℕ} {a b : ℕ → ℕ}
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (j : Fin t) → OrientedPerfectPairing (b j.val))

abbrev Node (i : Fin s) := Σ j : Fin t, Fin (P j).count → Bool ⊕ Fin (Q i).count
abbrev Recipe := (i : Fin s) → List (Node Q P i)
variable (recipe : Recipe Q P)

abbrev dataEncoding (t : ℕ) := framedListEncoding (pairEncoding (labelEncoding t) addressesEncoding)

def factor {i : Fin s} (r : Raw s) (v : ℕ) (node : Node Q P i) : Fin t × List ℕ :=
  (node.1,List.ofFn (fun j => M.port Q r v (node.2 j)))
def rowFor (r : Raw s) (v : ℕ) (i : Fin s) : List (Fin t × List ℕ) :=
  (recipe i).map (factor Q P r v)
def row (r : Raw s) (v : Fin r.labels.length) : List (Fin t × List ℕ) :=
  rowFor Q P recipe r v.val (r.labels.get v)
def data (r : Raw s) : List (Fin t × List ℕ) :=
  (List.finRange r.labels.length).flatMap (row Q P recipe r)
def query (r : Raw s) : Raw t :=
  ⟨r.variables,(data Q P recipe r).map Prod.fst,(data Q P recipe r).flatMap Prod.snd⟩

def factorComputes {i : Fin s} (node : Node Q P i) :
    Computes (M.rowEncoding s) (pairEncoding (labelEncoding t) addressesEncoding)
      (fun x => factor Q P x.1 x.2.val node) := by
  let ps := fixedListComputes (M.rowEncoding s) encodingNatBool
    (fun x j => M.port Q x.1 x.2.val (node.2 j))
    (fun j => M.portComputes Q (node.2 j)) (List.finRange (P node.1).count)
  refine congrComputes (pairComputes (constantComputes (M.rowEncoding s) (labelEncoding t) node.1) ps) ?_
  intro x
  dsimp only [factor]
  rw [←List.ofFn_eq_map]

def rowForComputes (i : Fin s) : Computes (M.rowEncoding s) (dataEncoding t)
    (fun x => rowFor Q P recipe x.1 x.2.val i) :=
  fixedListComputes (M.rowEncoding s) (pairEncoding (labelEncoding t) addressesEncoding)
    (fun x node => factor Q P x.1 x.2.val node) (factorComputes Q P) (recipe i)

def rowComputes : Computes (M.rowEncoding s) (dataEncoding t) (fun x => row Q P recipe x.1 x.2) :=
  chooseComputes (M.rowEncoding s) (dataEncoding t) s (fun x => x.1.labels.get x.2)
    (fun x i => rowFor Q P recipe x.1 x.2.val i) M.labelIndexComputes (rowForComputes Q P recipe)

def dataComputes : Computes (encoding s) (dataEncoding t) (data Q P recipe) :=
  congrComputes ((GeneralEOSignedParityProgram.tabulate (encoding s) (dataEncoding t)
    (fun r => r.labels.length) (labelsComputes.andThen (W.lengthComputes (labelEncoding s)))
    (row Q P recipe) (rowComputes Q P recipe)).andThen
      (W.flatten (pairEncoding (labelEncoding t) addressesEncoding)))
    (fun _ => by simp [data,List.flatMap_def])

def queryComputes : Computes (encoding s) (encoding t) (query Q P recipe) := by
  let ds := dataComputes Q P recipe
  let ls := ds.andThen (W.mapComputes (pairEncoding (labelEncoding t) addressesEncoding)
    (labelEncoding t) Prod.fst (Wiring.firstComputes (labelEncoding t) addressesEncoding))
  let ps := (ds.andThen (W.mapComputes (pairEncoding (labelEncoding t) addressesEncoding)
    addressesEncoding Prod.snd (Wiring.secondComputes (labelEncoding t) addressesEncoding))).andThen
      (W.flatten encodingNatBool)
  exact recode (pairComputes variablesComputes (pairComputes ls ps)) id
    (fun _ => rfl) (fun r => by simp only [Function.comp_def,List.flatMap_def]; rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleRaw
