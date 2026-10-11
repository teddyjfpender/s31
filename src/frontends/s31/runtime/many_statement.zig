//! Public statement wire format for the experimental source-pinned V4 CLI.
pub const schema_name = "s31-many-public-words-v4";

pub const Statement = struct {
    schema: []const u8,
    public_words: [8]u32,
};
