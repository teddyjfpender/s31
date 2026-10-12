//! Public statement wire format for the experimental source-pinned pair CLI.
pub const schema_name = "s31-pair-public-words-v1";

pub const Statement = struct {
    schema: []const u8,
    public_words: [8]u32,
};
