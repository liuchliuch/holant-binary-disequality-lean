import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortAnchorWitness

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def arep3888State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 38)]

def arep3888Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3888Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3888Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3888Node0Reductions arep3888Node0Children

theorem arep3888_cached_checked :
    arep3888Node0.check (cachedIntegerProblem arep3888State) (integerInitialRows arep3888State) = true := by
  decide +kernel

theorem arep3888_checked :
    arep3888Node0.check (integerProblem arep3888State) (integerInitialRows arep3888State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3888_cached_checked

theorem arep3888_solved : Solved arep3888State :=
  solved_of_integer_certificate arep3888State arep3888Node0 arep3888_checked

theorem arep3888_representative : Solved (stateEquiv (representativeCode 3888)) := by
  have he : stateEquiv (representativeCode 3888) = arep3888State := by decide +kernel
  rw [he]
  exact arep3888_solved

theorem anchorEntry2192_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2192))) := by
  have he : anchorRepresentative 2192 = 3888 := by decide +kernel
  rw [he]
  exact arep3888_representative

def arep3889State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 39)]

def arep3889Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3889Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3889Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3889Node0Reductions arep3889Node0Children

theorem arep3889_cached_checked :
    arep3889Node0.check (cachedIntegerProblem arep3889State) (integerInitialRows arep3889State) = true := by
  decide +kernel

theorem arep3889_checked :
    arep3889Node0.check (integerProblem arep3889State) (integerInitialRows arep3889State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3889_cached_checked

theorem arep3889_solved : Solved arep3889State :=
  solved_of_integer_certificate arep3889State arep3889Node0 arep3889_checked

theorem arep3889_representative : Solved (stateEquiv (representativeCode 3889)) := by
  have he : stateEquiv (representativeCode 3889) = arep3889State := by decide +kernel
  rw [he]
  exact arep3889_solved

theorem anchorEntry2193_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2193))) := by
  have he : anchorRepresentative 2193 = 3889 := by decide +kernel
  rw [he]
  exact arep3889_representative

def arep3890State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 40)]

def arep3890Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(10,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(2)⟩ : GZ)),(8,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3890Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3890Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3890Node0Reductions arep3890Node0Children

theorem arep3890_cached_checked :
    arep3890Node0.check (cachedIntegerProblem arep3890State) (integerInitialRows arep3890State) = true := by
  decide +kernel

theorem arep3890_checked :
    arep3890Node0.check (integerProblem arep3890State) (integerInitialRows arep3890State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3890_cached_checked

theorem arep3890_solved : Solved arep3890State :=
  solved_of_integer_certificate arep3890State arep3890Node0 arep3890_checked

theorem arep3890_representative : Solved (stateEquiv (representativeCode 3890)) := by
  have he : stateEquiv (representativeCode 3890) = arep3890State := by decide +kernel
  rw [he]
  exact arep3890_solved

theorem anchorEntry2194_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2194))) := by
  have he : anchorRepresentative 2194 = 3890 := by decide +kernel
  rw [he]
  exact arep3890_representative

def arep3891State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 41)]

def arep3891Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(0),(3)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 14, weights := [(5,(⟨(0),(3)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-4),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(2),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 14, weights := [(5,(⟨(0),(3)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-4),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3891Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3891Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3891Node0Reductions arep3891Node0Children

theorem arep3891_cached_checked :
    arep3891Node0.check (cachedIntegerProblem arep3891State) (integerInitialRows arep3891State) = true := by
  decide +kernel

theorem arep3891_checked :
    arep3891Node0.check (integerProblem arep3891State) (integerInitialRows arep3891State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3891_cached_checked

theorem arep3891_solved : Solved arep3891State :=
  solved_of_integer_certificate arep3891State arep3891Node0 arep3891_checked

theorem arep3891_representative : Solved (stateEquiv (representativeCode 3891)) := by
  have he : stateEquiv (representativeCode 3891) = arep3891State := by decide +kernel
  rw [he]
  exact arep3891_solved

theorem anchorEntry2195_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2195))) := by
  have he : anchorRepresentative 2195 = 3891 := by decide +kernel
  rw [he]
  exact arep3891_representative

def arep3892State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 42)]

def arep3892Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 16, weights := [(5,(⟨(0),(-3)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(5),(0)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,1),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,1),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,(⟨(5),(0)⟩ : GZ)),(8,(⟨(0),(-4)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-5)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(-4)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3892Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3892Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3892Node0Reductions arep3892Node0Children

theorem arep3892_cached_checked :
    arep3892Node0.check (cachedIntegerProblem arep3892State) (integerInitialRows arep3892State) = true := by
  decide +kernel

theorem arep3892_checked :
    arep3892Node0.check (integerProblem arep3892State) (integerInitialRows arep3892State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3892_cached_checked

theorem arep3892_solved : Solved arep3892State :=
  solved_of_integer_certificate arep3892State arep3892Node0 arep3892_checked

theorem arep3892_representative : Solved (stateEquiv (representativeCode 3892)) := by
  have he : stateEquiv (representativeCode 3892) = arep3892State := by decide +kernel
  rw [he]
  exact arep3892_solved

theorem anchorEntry2196_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2196))) := by
  have he : anchorRepresentative 2196 = 3892 := by decide +kernel
  rw [he]
  exact arep3892_representative

def arep3893State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 43)]

def arep3893Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(16,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-3)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3893Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3893Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3893Node0Reductions arep3893Node0Children

theorem arep3893_cached_checked :
    arep3893Node0.check (cachedIntegerProblem arep3893State) (integerInitialRows arep3893State) = true := by
  decide +kernel

theorem arep3893_checked :
    arep3893Node0.check (integerProblem arep3893State) (integerInitialRows arep3893State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3893_cached_checked

theorem arep3893_solved : Solved arep3893State :=
  solved_of_integer_certificate arep3893State arep3893Node0 arep3893_checked

theorem arep3893_representative : Solved (stateEquiv (representativeCode 3893)) := by
  have he : stateEquiv (representativeCode 3893) = arep3893State := by decide +kernel
  rw [he]
  exact arep3893_solved

theorem anchorEntry2197_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2197))) := by
  have he : anchorRepresentative 2197 = 3893 := by decide +kernel
  rw [he]
  exact arep3893_representative

def arep3894State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 44)]

def arep3894Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,1),(10,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(7,(⟨(0),(2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(7,1),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3894Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3894Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3894Node0Reductions arep3894Node0Children

theorem arep3894_cached_checked :
    arep3894Node0.check (cachedIntegerProblem arep3894State) (integerInitialRows arep3894State) = true := by
  decide +kernel

theorem arep3894_checked :
    arep3894Node0.check (integerProblem arep3894State) (integerInitialRows arep3894State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3894_cached_checked

theorem arep3894_solved : Solved arep3894State :=
  solved_of_integer_certificate arep3894State arep3894Node0 arep3894_checked

theorem arep3894_representative : Solved (stateEquiv (representativeCode 3894)) := by
  have he : stateEquiv (representativeCode 3894) = arep3894State := by decide +kernel
  rw [he]
  exact arep3894_solved

theorem anchorEntry2198_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2198))) := by
  have he : anchorRepresentative 2198 = 3894 := by decide +kernel
  rw [he]
  exact arep3894_representative

def arep3895State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 45)]

def arep3895Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3895Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3895Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3895Node0Reductions arep3895Node0Children

theorem arep3895_cached_checked :
    arep3895Node0.check (cachedIntegerProblem arep3895State) (integerInitialRows arep3895State) = true := by
  decide +kernel

theorem arep3895_checked :
    arep3895Node0.check (integerProblem arep3895State) (integerInitialRows arep3895State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3895_cached_checked

theorem arep3895_solved : Solved arep3895State :=
  solved_of_integer_certificate arep3895State arep3895Node0 arep3895_checked

theorem arep3895_representative : Solved (stateEquiv (representativeCode 3895)) := by
  have he : stateEquiv (representativeCode 3895) = arep3895State := by decide +kernel
  rw [he]
  exact arep3895_solved

theorem anchorEntry2199_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2199))) := by
  have he : anchorRepresentative 2199 = 3895 := by decide +kernel
  rw [he]
  exact arep3895_representative

def arep3897State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 32),some (directionEquiv 47)]

def arep3897Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(4)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(4)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3897Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3897Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3897Node0Reductions arep3897Node0Children

theorem arep3897_cached_checked :
    arep3897Node0.check (cachedIntegerProblem arep3897State) (integerInitialRows arep3897State) = true := by
  decide +kernel

theorem arep3897_checked :
    arep3897Node0.check (integerProblem arep3897State) (integerInitialRows arep3897State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3897_cached_checked

theorem arep3897_solved : Solved arep3897State :=
  solved_of_integer_certificate arep3897State arep3897Node0 arep3897_checked

theorem arep3897_representative : Solved (stateEquiv (representativeCode 3897)) := by
  have he : stateEquiv (representativeCode 3897) = arep3897State := by decide +kernel
  rw [he]
  exact arep3897_solved

theorem anchorEntry2200_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2200))) := by
  have he : anchorRepresentative 2200 = 3897 := by decide +kernel
  rw [he]
  exact arep3897_representative

def arep3932State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 33),some (directionEquiv 33)]

def arep3932Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3932Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3932Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3932Node0Reductions arep3932Node0Children

theorem arep3932_cached_checked :
    arep3932Node0.check (cachedIntegerProblem arep3932State) (integerInitialRows arep3932State) = true := by
  decide +kernel

theorem arep3932_checked :
    arep3932Node0.check (integerProblem arep3932State) (integerInitialRows arep3932State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3932_cached_checked

theorem arep3932_solved : Solved arep3932State :=
  solved_of_integer_certificate arep3932State arep3932Node0 arep3932_checked

theorem arep3932_representative : Solved (stateEquiv (representativeCode 3932)) := by
  have he : stateEquiv (representativeCode 3932) = arep3932State := by decide +kernel
  rw [he]
  exact arep3932_solved

theorem anchorEntry2201_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2201))) := by
  have he : anchorRepresentative 2201 = 3932 := by decide +kernel
  rw [he]
  exact arep3932_representative

def arep3933State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 33),some (directionEquiv 34)]

def arep3933Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-3)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(3)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 24, weights := [(5,1),(6,(⟨(-5),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 14, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-4)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(3)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-4)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(7),(0)⟩ : GZ)),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(5)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(4)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3933Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3933Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3933Node0Reductions arep3933Node0Children

theorem arep3933_cached_checked :
    arep3933Node0.check (cachedIntegerProblem arep3933State) (integerInitialRows arep3933State) = true := by
  decide +kernel

theorem arep3933_checked :
    arep3933Node0.check (integerProblem arep3933State) (integerInitialRows arep3933State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3933_cached_checked

theorem arep3933_solved : Solved arep3933State :=
  solved_of_integer_certificate arep3933State arep3933Node0 arep3933_checked

theorem arep3933_representative : Solved (stateEquiv (representativeCode 3933)) := by
  have he : stateEquiv (representativeCode 3933) = arep3933State := by decide +kernel
  rw [he]
  exact arep3933_solved

theorem anchorEntry2202_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2202))) := by
  have he : anchorRepresentative 2202 = 3933 := by decide +kernel
  rw [he]
  exact arep3933_representative

def arep3934State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 33),some (directionEquiv 35)]

def arep3934Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(7),(0)⟩ : GZ)),(6,(⟨(5),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-6),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(4)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-4)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(12,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(5),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 12, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(5),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,1),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-4)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(7),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(-4),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(5)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,1),(8,(⟨(0),(-2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3934Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3934Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3934Node0Reductions arep3934Node0Children

theorem arep3934_cached_checked :
    arep3934Node0.check (cachedIntegerProblem arep3934State) (integerInitialRows arep3934State) = true := by
  decide +kernel

theorem arep3934_checked :
    arep3934Node0.check (integerProblem arep3934State) (integerInitialRows arep3934State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3934_cached_checked

theorem arep3934_solved : Solved arep3934State :=
  solved_of_integer_certificate arep3934State arep3934Node0 arep3934_checked

theorem arep3934_representative : Solved (stateEquiv (representativeCode 3934)) := by
  have he : stateEquiv (representativeCode 3934) = arep3934State := by decide +kernel
  rw [he]
  exact arep3934_solved

theorem anchorEntry2203_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2203))) := by
  have he : anchorRepresentative 2203 = 3934 := by decide +kernel
  rw [he]
  exact arep3934_representative

def arep3935State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 33),some (directionEquiv 36)]

def arep3935Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(5),(0)⟩ : GZ)),(7,(⟨(0),(-3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(12,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3935Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3935Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3935Node0Reductions arep3935Node0Children

theorem arep3935_cached_checked :
    arep3935Node0.check (cachedIntegerProblem arep3935State) (integerInitialRows arep3935State) = true := by
  decide +kernel

theorem arep3935_checked :
    arep3935Node0.check (integerProblem arep3935State) (integerInitialRows arep3935State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3935_cached_checked

theorem arep3935_solved : Solved arep3935State :=
  solved_of_integer_certificate arep3935State arep3935Node0 arep3935_checked

theorem arep3935_representative : Solved (stateEquiv (representativeCode 3935)) := by
  have he : stateEquiv (representativeCode 3935) = arep3935State := by decide +kernel
  rw [he]
  exact arep3935_solved

theorem anchorEntry2204_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2204))) := by
  have he : anchorRepresentative 2204 = 3935 := by decide +kernel
  rw [he]
  exact arep3935_representative

def arep3937State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 33),some (directionEquiv 38)]

def arep3937Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-3)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(5),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(4),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3937Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3937Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3937Node0Reductions arep3937Node0Children

theorem arep3937_cached_checked :
    arep3937Node0.check (cachedIntegerProblem arep3937State) (integerInitialRows arep3937State) = true := by
  decide +kernel

theorem arep3937_checked :
    arep3937Node0.check (integerProblem arep3937State) (integerInitialRows arep3937State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3937_cached_checked

theorem arep3937_solved : Solved arep3937State :=
  solved_of_integer_certificate arep3937State arep3937Node0 arep3937_checked

theorem arep3937_representative : Solved (stateEquiv (representativeCode 3937)) := by
  have he : stateEquiv (representativeCode 3937) = arep3937State := by decide +kernel
  rw [he]
  exact arep3937_solved

theorem anchorEntry2205_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2205))) := by
  have he : anchorRepresentative 2205 = 3937 := by decide +kernel
  rw [he]
  exact arep3937_representative

def arep3938State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 33),some (directionEquiv 39)]

def arep3938Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(3)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 24, weights := [(5,(⟨(5),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(3)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 14, weights := [(5,(⟨(0),(3)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(4)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(-3),(0)⟩ : GZ)),(6,(⟨(7),(0)⟩ : GZ)),(7,(⟨(0),(-5)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-4)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(6,(⟨(0),(4)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-2),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(2)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3938Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3938Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3938Node0Reductions arep3938Node0Children

theorem arep3938_cached_checked :
    arep3938Node0.check (cachedIntegerProblem arep3938State) (integerInitialRows arep3938State) = true := by
  decide +kernel

theorem arep3938_checked :
    arep3938Node0.check (integerProblem arep3938State) (integerInitialRows arep3938State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3938_cached_checked

theorem arep3938_solved : Solved arep3938State :=
  solved_of_integer_certificate arep3938State arep3938Node0 arep3938_checked

theorem arep3938_representative : Solved (stateEquiv (representativeCode 3938)) := by
  have he : stateEquiv (representativeCode 3938) = arep3938State := by decide +kernel
  rw [he]
  exact arep3938_solved

theorem anchorEntry2206_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2206))) := by
  have he : anchorRepresentative 2206 = 3938 := by decide +kernel
  rw [he]
  exact arep3938_representative

def arep3939State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 33),some (directionEquiv 40)]

def arep3939Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(4)⟩ : GZ)),(7,1),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(4)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ)),(10,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(4)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(4)⟩ : GZ)),(7,1),(8,(⟨(0),(-3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(2)⟩ : GZ)),(7,1),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(-4)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-3),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-2)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(3),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(4)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-4)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(3)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(2)⟩ : GZ)),(6,(⟨(0),(-4)⟩ : GZ)),(7,(⟨(-3),(0)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3939Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3939Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3939Node0Reductions arep3939Node0Children

theorem arep3939_cached_checked :
    arep3939Node0.check (cachedIntegerProblem arep3939State) (integerInitialRows arep3939State) = true := by
  decide +kernel

theorem arep3939_checked :
    arep3939Node0.check (integerProblem arep3939State) (integerInitialRows arep3939State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3939_cached_checked

theorem arep3939_solved : Solved arep3939State :=
  solved_of_integer_certificate arep3939State arep3939Node0 arep3939_checked

theorem arep3939_representative : Solved (stateEquiv (representativeCode 3939)) := by
  have he : stateEquiv (representativeCode 3939) = arep3939State := by decide +kernel
  rw [he]
  exact arep3939_solved

theorem anchorEntry2207_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 2207))) := by
  have he : anchorRepresentative 2207 = 3939 := by decide +kernel
  rw [he]
  exact arep3939_representative

theorem anchorBatch137 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 (16*137+i.val))))) := by
  fin_cases i
  · exact anchorEntry2192_solved
  · exact anchorEntry2193_solved
  · exact anchorEntry2194_solved
  · exact anchorEntry2195_solved
  · exact anchorEntry2196_solved
  · exact anchorEntry2197_solved
  · exact anchorEntry2198_solved
  · exact anchorEntry2199_solved
  · exact anchorEntry2200_solved
  · exact anchorEntry2201_solved
  · exact anchorEntry2202_solved
  · exact anchorEntry2203_solved
  · exact anchorEntry2204_solved
  · exact anchorEntry2205_solved
  · exact anchorEntry2206_solved
  · exact anchorEntry2207_solved

end
end Holant.Pauli.ExoticKlein.SixPort
