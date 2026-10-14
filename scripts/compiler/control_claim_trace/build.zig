//! Isolated test tool; no production S31 source or build graph changes.
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const opts = .{ .target = target, .optimize = optimize };
    const cpu = b.dependency("stwo_circuit_cpu_integration", opts).module("stwo_circuit_cpu_integration");
    const core = cpu.import_table.get("stwo_core") orelse @panic("missing core");
    const circuit = cpu.import_table.get("stwo_circuit_frontend") orelse @panic("missing circuit");
    const prover = cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover");
    const cairo = cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo");
    const postcard = b.createModule(.{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/interop/postcard.zig") },
        .target = target, .optimize = optimize,
    });
    postcard.addImport("stwo_core", core);
    const official_air = b.createModule(.{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin") },
    });
    const sha = b.createModule(.{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/frontends/riscv/sha256_s31_provider.zig") },
        .target = target, .optimize = optimize,
    });
    sha.addImport("stwo_core", core);
    sha.addImport("stwo_prover_engine", prover);
    const s31 = b.createModule(.{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../src/frontends/s31/mod.zig") },
        .target = target, .optimize = optimize,
    });
    s31.addImport("stwo_core", core);
    s31.addImport("stwo_prover_engine", prover);
    s31.addImport("stwo_circuit_frontend", circuit);
    s31.addImport("stwo_circuit_cpu_integration", cpu);
    s31.addImport("stwo_cairo_frontend", cairo);
    s31.addImport("interop_postcard", postcard);
    s31.addImport("s31_air_programs", official_air);
    s31.addImport("s31_poseidon_ref", sha);
    s31.addImport("s31_sha_provider", sha);
    const root = b.createModule(.{
        .root_source_file = b.path("main.zig"), .target = target, .optimize = optimize,
    });
    root.addImport("stwo_core", core);
    root.addImport("stwo_circuit_frontend", circuit);
    root.addImport("stwo_circuit_cpu_integration", cpu);
    root.addImport("stwo_prover_engine", prover);
    root.addImport("interop_postcard", postcard);
    root.addImport("stwo_s31_prototype", s31);
    const executable = b.addExecutable(.{ .name = "s31-control-claim-trace", .root_module = root });
    const run = b.addRunArtifact(executable);
    if (b.args) |args| run.addArgs(args);
    b.step("audit", "Reconstruct one transparent control proof's committed trace")
        .dependOn(&run.step);
}
