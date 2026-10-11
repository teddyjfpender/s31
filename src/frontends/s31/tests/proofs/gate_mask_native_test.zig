//! Independent 512-row Gate predecessor oracle for the source mask utility.
//! This checks native index arithmetic, not OODS opening authentication.
const std = @import("std");
const utils = @import("stwo_utils");

fn reverseNine(value: usize) usize {
    var input = value;
    var output: usize = 0;
    for (0..9) |_| {
        output = (output << 1) | (input & 1);
        input >>= 1;
    }
    return output;
}

fn expectedPrevious(storage_row: usize) usize {
    const circle_row = reverseNine(storage_row);
    const coset_row = if (circle_row < 256)
        2 * circle_row
    else
        2 * (511 - circle_row) + 1;
    const previous_coset_row = (coset_row + 511) % 512;
    const previous_circle_row = if (previous_coset_row % 2 == 0)
        previous_coset_row / 2
    else
        (1024 - previous_coset_row) / 2;
    return reverseNine(previous_circle_row);
}

test "Gate source predecessor matches 512-row Lean formula on every row" {
    for (0..512) |row| {
        try std.testing.expectEqual(expectedPrevious(row),
            utils.previousBitReversedCircleDomainIndex(row, 9, 9));
        try std.testing.expectEqual(row,
            utils.offsetBitReversedCircleDomainIndex(row, 9, 9, 0));
    }
}
