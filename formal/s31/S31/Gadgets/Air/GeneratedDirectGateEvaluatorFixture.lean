-- Generated from checked direct Gate package plus a documented test vector.
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Interaction cells are synthetic and are not proof openings.
import S31.Gadgets.Air.DirectGateEvaluatorCells

namespace S31.Gadgets.Air.GeneratedDirectGateEvaluatorFixture

open S31.Gadgets.Air.DirectGateEvaluatorCells

-- Direct trace row 502.
def sourceFirst : Cells :=
  { localFixed := ![0, 0, 1, 0, 22, 22, 23, 2],
    main := ![0, 1, 2, 7, 0, 1, 2, 7, 0, 1, 4, 49],
    interaction := ![1, 2, 3, 4, 5, 6, 7, 8],
    previousInteraction := ![9, 10, 11, 12, 13, 14, 15, 16] }

-- Direct trace row 503.
def sourceSecond : Cells :=
  { localFixed := ![0, 0, 1, 0, 23, 23, 24, 4],
    main := ![0, 1, 4, 49, 0, 1, 4, 49, 0, 1, 16, 2401],
    interaction := ![17, 18, 19, 20, 21, 22, 23, 24],
    previousInteraction := ![25, 26, 27, 28, 29, 30, 31, 32] }

-- Direct trace row 502.
def changedFixed : Cells :=
  { localFixed := ![0, 1, 0, 0, 22, 22, 23, 2],
    main := ![0, 1, 2, 7, 0, 1, 2, 7, 0, 1, 4, 49],
    interaction := ![1, 2, 3, 4, 5, 6, 7, 8],
    previousInteraction := ![9, 10, 11, 12, 13, 14, 15, 16] }

-- Direct trace row 502.
def changedMain : Cells :=
  { localFixed := ![0, 0, 1, 0, 22, 22, 23, 2],
    main := ![0, 1, 2, 7, 0, 1, 2, 7, 49, 1, 4, 0],
    interaction := ![1, 2, 3, 4, 5, 6, 7, 8],
    previousInteraction := ![9, 10, 11, 12, 13, 14, 15, 16] }

-- Direct trace row 502.
def changedInteraction : Cells :=
  { localFixed := ![0, 0, 1, 0, 22, 22, 23, 2],
    main := ![0, 1, 2, 7, 0, 1, 2, 7, 0, 1, 4, 49],
    interaction := ![5, 2, 3, 4, 1, 6, 7, 8],
    previousInteraction := ![9, 10, 11, 12, 13, 14, 15, 16] }

-- Direct trace row 502.
def changedPrevious : Cells :=
  { localFixed := ![0, 0, 1, 0, 22, 22, 23, 2],
    main := ![0, 1, 2, 7, 0, 1, 2, 7, 0, 1, 4, 49],
    interaction := ![1, 2, 3, 4, 5, 6, 7, 8],
    previousInteraction := ![9, 10, 11, 12, 14, 14, 15, 16] }

theorem sourceFirst_arithmetic : arithmetic sourceFirst = List.replicate 9 0 := by decide

theorem sourceSecond_arithmetic : arithmetic sourceSecond = List.replicate 9 0 := by decide

theorem changed_fixed_detected : arithmetic changedFixed ≠ List.replicate 9 0 := by decide
theorem changed_main_detected : arithmetic changedMain ≠ List.replicate 9 0 := by decide
theorem changed_interaction_detected :
    pair sourceFirst 2 7 ≠ pair changedInteraction 2 7 := by decide

theorem changed_previous_detected :
    last sourceFirst 2 7 11 512 ≠ last changedPrevious 2 7 11 512 := by decide

theorem sourceFirst_pair_replay : pair sourceFirst 2 7 = ⟨⟨2097732206, 1413912158⟩, ⟨2120868237, 680340669⟩⟩ := by decide
theorem sourceFirst_last_replay : last sourceFirst 2 7 11 512 = ⟨⟨184868098, 511415914⟩, ⟨133060776, 1902189285⟩⟩ := by decide

theorem sourceSecond_pair_replay : pair sourceSecond 2 7 = ⟨⟨1856747042, 240738752⟩, ⟨15503833, 1937752561⟩⟩ := by decide
theorem sourceSecond_last_replay : last sourceSecond 2 7 11 512 = ⟨⟨932462148, 898222739⟩, ⟨519792143, 141361547⟩⟩ := by decide

end S31.Gadgets.Air.GeneratedDirectGateEvaluatorFixture
