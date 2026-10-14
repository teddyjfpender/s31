const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const opts = .{ .target = target, .optimize = optimize };
    const cpu = b.dependency("stwo_circuit_cpu_integration", opts).module("stwo_circuit_cpu_integration");
    const core = cpu.import_table.get("stwo_core") orelse @panic("circuit CPU module is missing core");
    const circuit = cpu.import_table.get("stwo_circuit_frontend") orelse @panic("circuit CPU module is missing frontend");
    const wire = cpu.import_table.get("stwo_circuit_recursion_wire") orelse @panic("circuit CPU module is missing wire");
    const selected_source = b.option([]const u8, "s31-source", "Absolute path to a normalized S31 source file");
    const source_asset: std.Build.LazyPath = if (selected_source) |path|
        .{ .cwd_relative = path }
    else
        b.path("examples/arithmetic/affine4.s31.json");
    const program_name = b.option([]const u8, "s31-name", "Build artifact name for the selected program") orelse "affine4";
    const source_version = b.option(u32, "s31-version", "Normalized source version (0, 1, or record ABI v2 for direct-gate/direct-mixed-general)") orelse 0;
    const lowering = b.option([]const u8, "s31-lowering", "gate, chip, sparse-gate, sparse-chip, sparse-wide-gate, direct-gate, direct-chip, experimental direct-pair/direct-many/direct-mixed/direct-mixed4/direct-mixed-general, sha-joint, sha-shift, or sha-fused proof lowering") orelse "gate";
    const channel_profile = b.option([]const u8, "s31-channel-profile", "legacy or raw-blake2s-rejection-v1 (ordinary gate only)") orelse "legacy";
    const raw_gate_channel = std.mem.eql(u8, channel_profile, "raw-blake2s-rejection-v1");
    if (!std.mem.eql(u8, channel_profile, "legacy") and
        (!raw_gate_channel or !std.mem.eql(u8, lowering, "gate")))
        @panic("raw BLAKE2s rejection channel requires ordinary gate lowering");
    const gate_manifest_version = b.option(u32, "s31-direct-gate-manifest-version", "Direct-gate manifest/proof envelope version (1 or 2)") orelse 1;
    if ((gate_manifest_version != 1 and gate_manifest_version != 2) or
        (gate_manifest_version == 2 and !std.mem.eql(u8, lowering, "direct-gate")))
        @panic("direct-gate manifest v2 requires direct-gate lowering");
    if (!std.mem.eql(u8, lowering, "gate") and !std.mem.eql(u8, lowering, "chip") and
        !std.mem.eql(u8, lowering, "sparse-gate") and !std.mem.eql(u8, lowering, "sparse-chip") and
        !std.mem.eql(u8, lowering, "sparse-wide-gate") and
        !std.mem.eql(u8, lowering, "direct-gate") and !std.mem.eql(u8, lowering, "direct-chip") and
        !std.mem.eql(u8, lowering, "direct-pair") and !std.mem.eql(u8, lowering, "direct-many") and
        !std.mem.eql(u8, lowering, "direct-mixed") and !std.mem.eql(u8, lowering, "direct-mixed4") and
        !std.mem.eql(u8, lowering, "direct-mixed-general") and
        !std.mem.eql(u8, lowering, "sha-joint") and !std.mem.eql(u8, lowering, "sha-shift") and
        !std.mem.eql(u8, lowering, "sha-fused"))
        @panic("invalid s31-lowering");
    const fri_fold_step = b.option(u32, "s31-fri-fold-step", "FRI folds per commitment for gate or sparse-wide-gate (1 or 4)") orelse 1;
    if ((fri_fold_step != 1 and fri_fold_step != 4) or
        (fri_fold_step != 1 and !std.mem.eql(u8, lowering, "gate") and !std.mem.eql(u8, lowering, "sparse-wide-gate")))
        @panic("FRI fold step 4 requires gate or sparse-wide-gate lowering; supported steps are 1 and 4");
    if (raw_gate_channel and fri_fold_step != 1)
        @panic("raw BLAKE2s Gate channel v1 supports FRI fold step 1 only");
    const mixed_lowering = std.mem.eql(u8, lowering, "direct-mixed") or std.mem.eql(u8, lowering, "direct-mixed4") or
        std.mem.eql(u8, lowering, "direct-mixed-general");
    const record_gate_lowering = source_version == 2 and std.mem.eql(u8, lowering, "direct-gate");
    if (mixed_lowering and source_version != 1 and
        !(source_version == 2 and std.mem.eql(u8, lowering, "direct-mixed-general")))
        @panic("experimental direct-mixed requires normalized S31 source version 1; general also admits record ABI v2");
    if ((mixed_lowering or record_gate_lowering) and selected_source == null)
        @panic("record or mixed lowering requires -Ds31-source=/absolute/path/to/source.s31.json");
    if (mixed_lowering or record_gate_lowering) {
        const source_bytes = std.fs.cwd().readFileAlloc(b.allocator, selected_source.?, 1 << 20) catch
            @panic("cannot read bounded source");
        defer b.allocator.free(source_bytes);
        var declared = std.json.parseFromSlice(struct { version: u32 }, b.allocator, source_bytes, .{
            .ignore_unknown_fields = true,
            .duplicate_field_behavior = .@"error",
        }) catch @panic("source is not normalized JSON with one version field");
        defer declared.deinit();
        if (declared.value.version != source_version) {
            if (mixed_lowering)
                @panic("-Ds31-version differs from embedded mixed source version");
            @panic("-Ds31-version differs from embedded record source version");
        }
    }
    const s31_options = b.addOptions();
    s31_options.addOption(bool, "chip_mode", std.mem.eql(u8, lowering, "chip") or std.mem.eql(u8, lowering, "sparse-chip") or std.mem.eql(u8, lowering, "direct-chip") or std.mem.eql(u8, lowering, "direct-pair") or std.mem.eql(u8, lowering, "direct-many") or mixed_lowering);
    s31_options.addOption(bool, "sparse_mode", std.mem.startsWith(u8, lowering, "sparse-"));
    s31_options.addOption(bool, "wide_mode", std.mem.eql(u8, lowering, "sparse-wide-gate"));
    s31_options.addOption(bool, "direct_mode", std.mem.startsWith(u8, lowering, "direct-"));
    s31_options.addOption(bool, "gate_manifest_v2", gate_manifest_version == 2);
    s31_options.addOption(bool, "raw_gate_channel", raw_gate_channel);
    s31_options.addOption(bool, "sha_joint_mode", std.mem.eql(u8, lowering, "sha-joint"));
    s31_options.addOption(bool, "sha_shift_mode", std.mem.eql(u8, lowering, "sha-shift"));
    s31_options.addOption(bool, "sha_fused_mode", std.mem.eql(u8, lowering, "sha-fused"));
    s31_options.addOption(u32, "fri_fold_step", fri_fold_step);
    s31_options.addOption([]const u8, "stdlib_lock_sha256", b.option([]const u8, "s31-stdlib-sha256", "Pinned S31 standard library lock digest") orelse "");

    const sha_postcard = b.createModule(.{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/interop/postcard.zig") }, .target = target, .optimize = optimize });
    sha_postcard.addImport("stwo_core", core);
    const official_air = b.createModule(.{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin") } });
    const frontend = b.addModule("stwo_s31_prototype", .{
        .root_source_file = b.path("mod.zig"),
        .target = target,
        .optimize = optimize,
    });
    frontend.addImport("stwo_core", core);
    frontend.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("circuit CPU module is missing prover engine"));
    frontend.addImport("stwo_circuit_frontend", circuit);
    frontend.addImport("stwo_circuit_cpu_integration", cpu);
    frontend.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    frontend.addImport("interop_postcard", sha_postcard);
    frontend.addImport("s31_air_programs", official_air);
    const sha_provider = b.createModule(.{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/frontends/riscv/sha256_s31_provider.zig") },
        .target = target,
        .optimize = optimize,
    });
    sha_provider.addImport("stwo_core", core);
    sha_provider.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    frontend.addImport("s31_poseidon_ref", sha_provider);
    frontend.addImport("s31_sha_provider", sha_provider);

    const tests = b.addRunArtifact(b.addTest(.{ .root_module = frontend }));
    const test_step = b.step("test", "Test the S31 prototype parser, evaluator and circuit compiler");
    test_step.dependOn(&tests.step);
    const public_physical_guard_root = b.createModule(.{
        .root_source_file = b.path("runtime/public_physical_guard.zig"),
        .target = target,
        .optimize = optimize,
    });
    public_physical_guard_root.addImport("stwo_core", core);
    public_physical_guard_root.addImport("stwo_circuit_frontend", circuit);
    public_physical_guard_root.addImport("s31_poseidon_ref", sha_provider);
    public_physical_guard_root.addImport("stwo_s31_prototype", frontend);
    const public_physical_guard_tests = b.addRunArtifact(b.addTest(.{ .root_module = public_physical_guard_root }));
    b.step("test-public-physical-guard", "Reject private and unsupported direct-Gate diagnostic exports")
        .dependOn(&public_physical_guard_tests.step);
    const canonical_cse_tests = b.addRunArtifact(b.addTest(.{
        .root_module = frontend,
        .filters = &.{"CSE"},
    }));
    b.step("test-canonical-cse", "Check source-to-canonical CSE bytes and verifier digest")
        .dependOn(&canonical_cse_tests.step);
    const record_parser_corpus_root = b.createModule(.{
        .root_source_file = b.path("tests/acceptance/record_abi/native_parser_corpus.zig"),
        .target = target,
        .optimize = optimize,
    });
    record_parser_corpus_root.addImport("stwo_s31_prototype", frontend);
    const record_parser_corpus = b.addRunArtifact(b.addExecutable(.{
        .name = "s31-record-statement-parser-corpus",
        .root_module = record_parser_corpus_root,
    }));
    if (b.args) |args| record_parser_corpus.addArgs(args);
    b.step("record-statement-parser-corpus", "Check compiled record claims in the Zig parser")
        .dependOn(&record_parser_corpus.step);
    const structural_witness_root = b.createModule(.{
        .root_source_file = b.path("tests/acceptance/compiler_correspondence/native_structural_witness_corpus.zig"),
        .target = target,
        .optimize = optimize,
    });
    structural_witness_root.addImport("stwo_core", core);
    structural_witness_root.addImport("stwo_circuit_frontend", circuit);
    structural_witness_root.addImport("stwo_circuit_cpu_integration", cpu);
    structural_witness_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    structural_witness_root.addImport("interop_postcard", sha_postcard);
    structural_witness_root.addImport("stwo_s31_prototype", frontend);
    const audit_fixed = b.createModule(.{ .root_source_file = b.path("runtime/public_fixed_commitment.zig"), .target = target, .optimize = optimize });
    audit_fixed.addImport("stwo_core", core);
    audit_fixed.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    audit_fixed.addImport("stwo_circuit_frontend", circuit);
    structural_witness_root.addImport("s31_audit_fixed_commitment", audit_fixed);
    const audit_main = b.createModule(.{ .root_source_file = b.path("runtime/public_main_commitment.zig"), .target = target, .optimize = optimize });
    audit_main.addImport("stwo_core", core);
    audit_main.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    audit_main.addImport("stwo_circuit_frontend", circuit);
    audit_main.addImport("stwo_circuit_cpu_integration", cpu);
    structural_witness_root.addImport("s31_audit_main_commitment", audit_main);
    const control_claim_trace_root = b.createModule(.{
        .root_source_file = b.path("tests/acceptance/compiler_correspondence/native_control_claim_trace.zig"),
        .target = target,
        .optimize = optimize,
    });
    control_claim_trace_root.addImport("stwo_core", core);
    control_claim_trace_root.addImport("stwo_circuit_frontend", circuit);
    control_claim_trace_root.addImport("stwo_circuit_cpu_integration", cpu);
    control_claim_trace_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    control_claim_trace_root.addImport("interop_postcard", sha_postcard);
    control_claim_trace_root.addImport("stwo_s31_prototype", frontend);
    const control_claim_trace = b.addExecutable(.{
        .name = "s31-control-claim-trace",
        .root_module = control_claim_trace_root,
    });
    b.step("control-claim-trace-build", "Build the noninstalled control proof trace audit")
        .dependOn(&control_claim_trace.step);
    const run_control_claim_trace = b.addRunArtifact(control_claim_trace);
    if (b.args) |args| run_control_claim_trace.addArgs(args);
    b.step("control-claim-trace", "Reconstruct one transparent control proof's committed trace")
        .dependOn(&run_control_claim_trace.step);
    const structural_witness = b.addRunArtifact(b.addExecutable(.{
        .name = "s31-structural-native-witness-corpus",
        .root_module = structural_witness_root,
    }));
    if (b.args) |args| structural_witness.addArgs(args);
    b.step("structural-native-witness-corpus", "Check bounded source node values against native direct Gate compiler")
        .dependOn(&structural_witness.step);
    const record_descriptor_corpus_root = b.createModule(.{
        .root_source_file = b.path("tests/acceptance/record_abi/native_descriptor_corpus.zig"),
        .target = target,
        .optimize = optimize,
    });
    record_descriptor_corpus_root.addImport("stwo_s31_prototype", frontend);
    const record_descriptor_corpus = b.addRunArtifact(b.addExecutable(.{
        .name = "s31-record-descriptor-parser-corpus",
        .root_module = record_descriptor_corpus_root,
    }));
    if (b.args) |args| record_descriptor_corpus.addArgs(args);
    b.step("record-descriptor-parser-corpus", "Check record ABI v2 descriptor shapes in the Zig parser")
        .dependOn(&record_descriptor_corpus.step);
    const pair_source_test_root = localEntry(b, "tests/proofs/private_pair_source_test.zig", target, optimize);
    pair_source_test_root.addImport("stwo_core", core);
    pair_source_test_root.addImport("stwo_circuit_frontend", circuit);
    pair_source_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    pair_source_test_root.addImport("stwo_s31_prototype", frontend);
    pair_source_test_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    pair_source_test_root.addImport("interop_postcard", sha_postcard);
    pair_source_test_root.addImport("s31_air_programs", official_air);
    pair_source_test_root.addImport("s31_sha_provider", sha_provider);
    pair_source_test_root.addImport("s31_poseidon_ref", sha_provider);
    pair_source_test_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
    pair_source_test_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
    pair_source_test_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
    pair_source_test_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
    pair_source_test_root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
    const pair_source_tests = b.addRunArtifact(b.addTest(.{ .root_module = pair_source_test_root, .filters = &.{"two-call source derives canonical plan"} }));
    b.step("test-pair-source", "Test source-derived two-call plan and typed V3 manifest").dependOn(&pair_source_tests.step);
    const pair_native_tests = b.addRunArtifact(b.addTest(.{ .root_module = pair_source_test_root, .filters = &.{"sealed pair native proof accepts"} }));
    b.step("test-pair-native", "Prove and natively verify the source-derived sealed two-call envelope").dependOn(&pair_native_tests.step);
    const pair_native_long_tests = b.addRunArtifact(b.addTest(.{ .root_module = pair_source_test_root, .filters = &.{"sealed pair native long-round lifting"} }));
    b.step("test-pair-native-long", "Check two-call PCS lifting when chip traces exceed the circuit trace").dependOn(&pair_native_long_tests.step);
    const many_call_source_root = localEntry(b, "language/bounded_call_admission.zig", target, optimize);
    many_call_source_root.addImport("stwo_core", core);
    many_call_source_root.addImport("stwo_circuit_frontend", circuit);
    many_call_source_root.addImport("s31_poseidon_ref", sha_provider);
    const many_call_source_tests = b.addRunArtifact(b.addTest(.{ .root_module = many_call_source_root }));
    b.step("test-bounded-call-source", "Test source-only bounded multi-call admission")
        .dependOn(&many_call_source_tests.step);
    const mixed_call_source_root = localEntry(b, "language/bounded_call_admission_v2.zig", target, optimize);
    mixed_call_source_root.addImport("stwo_core", core);
    mixed_call_source_root.addImport("stwo_circuit_frontend", circuit);
    mixed_call_source_root.addImport("s31_poseidon_ref", sha_provider);
    const mixed_call_source_tests = b.addRunArtifact(b.addTest(.{ .root_module = mixed_call_source_root }));
    b.step("test-mixed-call-source-v2", "Test source-only mixed square/add and mix4 call admission")
        .dependOn(&mixed_call_source_tests.step);
    const bounded_manifest_root = localEntry(b, "entry/bounded_component_manifest.zig", target, optimize);
    bounded_manifest_root.addImport("stwo_core", core);
    bounded_manifest_root.addImport("stwo_circuit_frontend", circuit);
    bounded_manifest_root.addImport("stwo_circuit_cpu_integration", cpu);
    bounded_manifest_root.addImport("s31_poseidon_ref", sha_provider);
    bounded_manifest_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
    bounded_manifest_root.addAnonymousImport("s31_many_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_many_boundary.zig") } });
    bounded_manifest_root.addAnonymousImport("s31_many_preflight_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig") } });
    bounded_manifest_root.addAnonymousImport("s31_many_direct_circuit_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig") } });
    bounded_manifest_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
    bounded_manifest_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
    bounded_manifest_root.addAnonymousImport("s31_tagged_many_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_chip.zig") } });
    bounded_manifest_root.addAnonymousImport("s31_tagged_many_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_bridge.zig") } });
    const bounded_manifest_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_manifest_root }));
    const descriptor_contract_root = localEntry(b, "runtime/component_descriptor_contract.zig", target, optimize);
    const descriptor_contract_tests = b.addRunArtifact(b.addTest(.{ .root_module = descriptor_contract_root }));
    const bounded_manifest_step = b.step("test-bounded-component-manifest", "Test source-derived 1..8-call V4 roster and descriptor contract");
    bounded_manifest_step.dependOn(&bounded_manifest_tests.step);
    bounded_manifest_step.dependOn(&descriptor_contract_tests.step);
    const bounded_binding_root = localEntry(b, "entry/bounded_compiled_binding.zig", target, optimize);
    bounded_binding_root.addImport("stwo_core", core);
    bounded_binding_root.addImport("stwo_circuit_frontend", circuit);
    bounded_binding_root.addImport("stwo_circuit_cpu_integration", cpu);
    bounded_binding_root.addImport("s31_sha_provider", sha_provider);
    bounded_binding_root.addImport("s31_poseidon_ref", sha_provider);
    bounded_binding_root.addImport("interop_postcard", sha_postcard);
    bounded_binding_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
    bounded_binding_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
    bounded_binding_root.addAnonymousImport("s31_many_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_many_boundary.zig") } });
    bounded_binding_root.addAnonymousImport("s31_many_preflight_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig") } });
    bounded_binding_root.addAnonymousImport("s31_many_direct_circuit_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig") } });
    bounded_binding_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
    bounded_binding_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
    bounded_binding_root.addAnonymousImport("s31_tagged_many_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_chip.zig") } });
    bounded_binding_root.addAnonymousImport("s31_tagged_many_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_bridge.zig") } });
    bounded_binding_root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
    bounded_binding_root.addAnonymousImport("s31_air_programs", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin") } });
    const bounded_binding_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"bounded"} }));
    b.step("test-bounded-compiled-binding", "Test compiled V4 endpoints and experimental native proof admission")
        .dependOn(&bounded_binding_tests.step);
    const many_native_matrix_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"V4 native count matrix"} }));
    b.step("test-many-native-matrix", "Prove and verify bounded V4 native envelopes for every count 2 through 8")
        .dependOn(&many_native_matrix_tests.step);
    const mixed_admission_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed composition admission"} }));
    b.step("test-mixed-composition-admission", "Inspect source-bound mixed pair/many AIR roster without proof admission")
        .dependOn(&mixed_admission_tests.step);
    const mixed_descriptor_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed descriptor"} }));
    b.step("test-mixed-descriptor", "Check source-bound mixed component descriptors for every bounded call count")
        .dependOn(&mixed_descriptor_tests.step);
    const mixed_registry_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed registry"} }));
    b.step("test-mixed-registry", "Check source-derived mixed registry and component manifests for every bounded call count")
        .dependOn(&mixed_registry_tests.step);
    const mixed_n4_witness_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed N4 witness audit"} }));
    b.step("test-mixed-n4-witness", "Audit source-bound N4 circuit, chip, and bridge base handoffs without proving")
        .dependOn(&mixed_n4_witness_tests.step);
    const mixed_trace_correspondence_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed N1 and N8 source base rows and proof envelope"} }));
    b.step("test-mixed-trace-correspondence", "Check exact N1/N8 native base rows and verified proof envelopes")
        .dependOn(&mixed_trace_correspondence_tests.step);
    const mixed_opening_authentication_tests = b.addRunArtifact(b.addTest(.{
        .root_module = bounded_binding_root,
        .filters = &.{"mixed circuit pair and many chip bridge queried openings authenticate to their roots"},
        .test_runner = .{ .path = b.path("tests/proofs/mixed_boundary/opening_test_runner.zig"), .mode = .simple },
    }));
    b.step("test-mixed-opening-authentication", "Reject changed queried values and Merkle paths in every mixed proof tree")
        .dependOn(&mixed_opening_authentication_tests.step);
    const mixed_producer_roster_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed N1 through N8 source logical producer roster"} }));
    const mixed_fork_multiplicity_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed fork counts every shared circuit-to-chip input in fixed multiplicity"} }));
    const mixed_producer_roster_step = b.step("test-mixed-producer-roster", "Check N1..8 and forked compiled Gate producer multiplicities against native fixed columns");
    mixed_producer_roster_step.dependOn(&mixed_producer_roster_tests.step);
    mixed_producer_roster_step.dependOn(&mixed_fork_multiplicity_tests.step);
    const mixed_native_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed sealed N3 native"} }));
    b.step("test-mixed-native", "Prove and verify source-pinned mixed N3 native envelopes")
        .dependOn(&mixed_native_tests.step);
    const mixed_n4_native_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed sealed N4 native"} }));
    b.step("test-mixed-n4-native", "Prove and verify source-pinned mixed N4 native envelopes")
        .dependOn(&mixed_n4_native_tests.step);
    const mixed_general_native_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed general sealed native"} }));
    b.step("test-mixed-general-native", "Prove and verify source-pinned mixed one-to-eight-call native envelopes")
        .dependOn(&mixed_general_native_tests.step);
    const mixed_record_word_domain_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed package raw verifier preserves the admitted public bit domain"} }));
    b.step("test-mixed-record-word-domain", "Reject out-of-domain record bit claims at the raw mixed proof API")
        .dependOn(&mixed_record_word_domain_tests.step);
    const mixed_trace_audit_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed general witness sidecar binds verified roots"} }));
    b.step("test-mixed-trace-audit", "Verify proof roots against an opt-in full-witness mixed trace audit")
        .dependOn(&mixed_trace_audit_tests.step);
    const mixed_trace_mutation_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed trace audit rejects interaction and bridge mutations"} }));
    b.step("test-mixed-trace-mutations", "Reject changed LogUp, bit-reversed chip, bridge, and interaction rows")
        .dependOn(&mixed_trace_mutation_tests.step);
    const mixed_circuit_mutation_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed trace audit checks reserved public and every gate row"} }));
    b.step("test-mixed-circuit-mutations", "Reject changed reserved, Gate, fixed, and main cells")
        .dependOn(&mixed_circuit_mutation_tests.step);
    const mixed_equal_public_sidecar_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed equal-public sidecar rejects wrong private selector"} }));
    b.step("test-mixed-equal-public-sidecar", "Reject a different private trace with the same public result at the main root")
        .dependOn(&mixed_equal_public_sidecar_tests.step);
    const mixed_selected_feeder_tests = b.addRunArtifact(b.addTest(.{ .root_module = bounded_binding_root, .filters = &.{"mixed selected feeder native"} }));
    b.step("test-mixed-selected-feeder", "Prove and verify both private-bit circuit-to-chip branches")
        .dependOn(&mixed_selected_feeder_tests.step);
    const square_export_root = localEntry(b, "tools/formal/export_square4_topology.zig", target, optimize);
    square_export_root.addImport("stwo_s31_prototype", frontend);
    square_export_root.addImport("stwo_circuit_frontend", circuit);
    square_export_root.addImport("stwo_core", core);
    const square_export = b.addRunArtifact(b.addExecutable(.{
        .name = "s31-export-square4-topology-lean",
        .root_module = square_export_root,
    }));
    square_export.addFileArg(source_asset);
    b.step("export-square4-topology-lean", "Print compiled square4 circuit topology as Lean source")
        .dependOn(&square_export.step);
    const mixed_fixed_export_root = localEntry(b, "tools/formal/export_mixed_fixed_rows.zig", target, optimize);
    mixed_fixed_export_root.addImport("stwo_core", core);
    mixed_fixed_export_root.addImport("stwo_circuit_frontend", circuit);
    mixed_fixed_export_root.addImport("stwo_circuit_cpu_integration", cpu);
    mixed_fixed_export_root.addImport("s31_sha_provider", sha_provider);
    mixed_fixed_export_root.addImport("s31_poseidon_ref", sha_provider);
    mixed_fixed_export_root.addImport("interop_postcard", sha_postcard);
    mixed_fixed_export_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_many_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_many_boundary.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_many_preflight_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_many_direct_circuit_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_tagged_many_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_chip.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_tagged_many_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_bridge.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
    mixed_fixed_export_root.addAnonymousImport("s31_air_programs", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin") } });
    const mixed_fixed_export = b.addRunArtifact(b.addExecutable(.{
        .name = "s31-export-mixed-fixed-rows",
        .root_module = mixed_fixed_export_root,
    }));
    b.step("export-mixed-fixed-rows", "Export N1/N8 source-pinned native selected Qm31 fixed rows")
        .dependOn(&mixed_fixed_export.step);
    const bitcoin_step_inspector_root = localEntry(b, "tools/inspect/inspect_bitcoin_fold_step.zig", target, optimize);
    bitcoin_step_inspector_root.addImport("stwo_s31_prototype", frontend);
    bitcoin_step_inspector_root.addImport("stwo_circuit_frontend", circuit);
    const bitcoin_step_inspector = b.addExecutable(.{
        .name = "s31-inspect-bitcoin-fold-step",
        .root_module = bitcoin_step_inspector_root,
    });
    b.step("inspect-bitcoin-fold-step", "Inspect witness-free Bitcoin fold-step circuit cost")
        .dependOn(&b.addRunArtifact(bitcoin_step_inspector).step);
    const bitcoin_fold_inspector_root = localEntry(b, "tools/inspect/inspect_bitcoin_chain_fold.zig", target, optimize);
    bitcoin_fold_inspector_root.addImport("stwo_s31_prototype", frontend);
    bitcoin_fold_inspector_root.addImport("stwo_core", core);
    bitcoin_fold_inspector_root.addImport("stwo_circuit_frontend", circuit);
    bitcoin_fold_inspector_root.addImport("stwo_circuit_cpu_integration", cpu);
    bitcoin_fold_inspector_root.addAnonymousImport("s31_air_projection", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") } });
    bitcoin_fold_inspector_root.addAnonymousImport("s31_fold_reference", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../design/s31/measurements/bitcoin/bitcoin-sparse-wide-fold-stages-v1-2026-10-07.json") } });
    const bitcoin_fold_inspector = b.addExecutable(.{
        .name = "s31-inspect-bitcoin-chain-fold",
        .root_module = bitcoin_fold_inspector_root,
    });
    b.step("inspect-bitcoin-chain-fold", "Inspect complete candidate Bitcoin chain-fold topology")
        .dependOn(&b.addRunArtifact(bitcoin_fold_inspector).step);
    const fused_fold_inspector_root = localEntry(b, "tools/inspect/inspect_bitcoin_chain_fold_fused.zig", target, optimize);
    fused_fold_inspector_root.addImport("stwo_s31_prototype", frontend);
    fused_fold_inspector_root.addImport("stwo_core", core);
    fused_fold_inspector_root.addImport("stwo_circuit_frontend", circuit);
    fused_fold_inspector_root.addImport("stwo_circuit_cpu_integration", cpu);
    fused_fold_inspector_root.addAnonymousImport("s31_air_projection", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") },
    });
    fused_fold_inspector_root.addAnonymousImport("s31_fold_reference", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../design/s31/measurements/bitcoin/bitcoin-sparse-wide-fold-stages-v1-2026-10-07.json") },
    });
    const fused_fold_inspector = b.addExecutable(.{
        .name = "s31-inspect-bitcoin-chain-fold-fused",
        .root_module = fused_fold_inspector_root,
    });
    b.step("inspect-bitcoin-chain-fold-fused", "Inspect fused-SHA Bitcoin chain-fold topology and private boundary")
        .dependOn(&b.addRunArtifact(fused_fold_inspector).step);
    const bitcoin_work_test_root = localEntry(b, "bitcoin/consensus/bitcoin_work.zig", target, optimize);
    bitcoin_work_test_root.addImport("stwo_core", core);
    bitcoin_work_test_root.addImport("stwo_circuit_frontend", circuit);
    const bitcoin_work_tests = b.addRunArtifact(b.addTest(.{ .root_module = bitcoin_work_test_root }));
    b.step("test-bitcoin-work", "Test checked Bitcoin work arithmetic")
        .dependOn(&bitcoin_work_tests.step);
    const bitcoin_fold_test_root = localEntry(b, "bitcoin/fold/bitcoin_chain_fold.zig", target, optimize);
    bitcoin_fold_test_root.addImport("stwo_s31_prototype", frontend);
    bitcoin_fold_test_root.addImport("stwo_core", core);
    bitcoin_fold_test_root.addImport("stwo_circuit_frontend", circuit);
    bitcoin_fold_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    const bitcoin_fold_tests = b.addRunArtifact(b.addTest(.{
        .root_module = bitcoin_fold_test_root,
        .filters = &.{"Bitcoin fold chooses a trusted base or the authenticated previous digest"},
    }));
    test_step.dependOn(&bitcoin_fold_tests.step);
    const external_sha_step_root = localEntry(b, "bitcoin/fold/bitcoin_fold_step.zig", target, optimize);
    external_sha_step_root.addImport("stwo_core", core);
    external_sha_step_root.addImport("stwo_circuit_frontend", circuit);
    external_sha_step_root.addImport("s31_sha_provider", sha_provider);
    external_sha_step_root.addImport("s31_poseidon_ref", sha_provider);
    const external_sha_step_tests = b.addRunArtifact(b.addTest(.{
        .root_module = external_sha_step_root,
        .filters = &.{ "external digest step matches", "external digest substitution", "direct recursive header kernel proves genesis-to-block-one link and PoW" },
    }));
    b.step("test-bitcoin-fold-step-external", "Test the external SHA digest Bitcoin fold-step constraints")
        .dependOn(&external_sha_step_tests.step);
    const bitcoin_anchor_test_root = localEntry(b, "bitcoin/fold/bitcoin_chain_anchor.zig", target, optimize);
    bitcoin_anchor_test_root.addImport("stwo_core", core);
    bitcoin_anchor_test_root.addImport("stwo_circuit_frontend", circuit);
    const bitcoin_anchor_tests = b.addRunArtifact(b.addTest(.{
        .root_module = bitcoin_anchor_test_root,
        .filters = &.{"Bitcoin checkpoint anchor has the same AIR in value and topology modes"},
    }));
    test_step.dependOn(&bitcoin_anchor_tests.step);
    const anchor_proof_test_root = localEntry(b, "bitcoin/tests/bitcoin_chain_anchor_proof_test.zig", target, optimize);
    anchor_proof_test_root.addImport("stwo_core", core);
    anchor_proof_test_root.addImport("stwo_circuit_frontend", circuit);
    anchor_proof_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    anchor_proof_test_root.addImport("stwo_s31_prototype", frontend);
    anchor_proof_test_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    anchor_proof_test_root.addImport("interop_postcard", sha_postcard);
    anchor_proof_test_root.addImport("s31_air_programs", official_air);
    anchor_proof_test_root.addAnonymousImport("s31_air_projection", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") },
    });
    const private_bridge_test_root = localEntry(b, "tests/proofs/private_boundary_proof_test.zig", target, optimize);
    private_bridge_test_root.addImport("stwo_s31_prototype", frontend);
    private_bridge_test_root.addImport("stwo_core", core);
    private_bridge_test_root.addImport("stwo_circuit_frontend", circuit);
    private_bridge_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    private_bridge_test_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    private_bridge_test_root.addImport("interop_postcard", sha_postcard);
    private_bridge_test_root.addImport("s31_air_programs", official_air);
    private_bridge_test_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
    private_bridge_test_root.addAnonymousImport("s31_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_boundary_bridge.zig") } });
    const private_bridge_test = b.addTest(.{ .root_module = private_bridge_test_root });
    const private_bridge_tests = b.addRunArtifact(private_bridge_test);
    b.step("check-private-boundary-proof", "Compile the private source-to-chip proof test")
        .dependOn(&private_bridge_test.step);
    b.step("test-private-boundary-proof", "Prove and verify the private source-to-chip boundary")
        .dependOn(&private_bridge_tests.step);
    test_step.dependOn(&private_bridge_tests.step);
    const sha_joint_test_root = localEntry(b, "sha/tests/sha_joint_prover_test.zig", target, optimize);
    sha_joint_test_root.addImport("stwo_core", core);
    sha_joint_test_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_joint_test_root.addImport("stwo_circuit_frontend", circuit);
    sha_joint_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_joint_test_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_joint_test_root.addImport("s31_sha_provider", sha_provider);
    sha_joint_test_root.addImport("s31_poseidon_ref", sha_provider);
    sha_joint_test_root.addImport("interop_postcard", sha_postcard);
    sha_joint_test_root.addImport("s31_air_programs", official_air);
    const sha_joint_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_joint_test_root }));
    b.step("test-sha-joint", "Compile and test one-proof circuit plus packed SHA integration")
        .dependOn(&sha_joint_tests.step);
    const sha_joint_batch2_test_root = localEntry(b, "sha/tests/sha_joint_batch2_prover_test.zig", target, optimize);
    sha_joint_batch2_test_root.addImport("stwo_core", core);
    sha_joint_batch2_test_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_joint_batch2_test_root.addImport("stwo_circuit_frontend", circuit);
    sha_joint_batch2_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_joint_batch2_test_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_joint_batch2_test_root.addImport("s31_sha_provider", sha_provider);
    sha_joint_batch2_test_root.addImport("s31_poseidon_ref", sha_provider);
    sha_joint_batch2_test_root.addImport("interop_postcard", sha_postcard);
    sha_joint_batch2_test_root.addImport("s31_air_programs", official_air);
    const sha_joint_batch2_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_joint_batch2_test_root }));
    b.step("test-sha-joint-batch2", "Prove and verify two private Bitcoin headers with one SHA AIR proof")
        .dependOn(&sha_joint_batch2_tests.step);
    const sha_round_direct_test_root = localEntry(b, "sha/tests/sha_round_direct_proof_test.zig", target, optimize);
    sha_round_direct_test_root.addImport("stwo_core", core);
    sha_round_direct_test_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_round_direct_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_round_direct_test_root.addImport("s31_sha_provider", sha_provider);
    sha_round_direct_test_root.addImport("interop_postcard", sha_postcard);
    const sha_round_direct_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_round_direct_test_root }));
    b.step("test-sha-round-direct", "Prove and natively verify the table-free SHA-256 round AIR")
        .dependOn(&sha_round_direct_tests.step);
    const sha_schedule_direct_test_root = localEntry(b, "sha/tests/sha_schedule_direct_proof_test.zig", target, optimize);
    sha_schedule_direct_test_root.addImport("stwo_core", core);
    sha_schedule_direct_test_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_schedule_direct_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_schedule_direct_test_root.addImport("s31_sha_provider", sha_provider);
    sha_schedule_direct_test_root.addImport("interop_postcard", sha_postcard);
    const sha_schedule_direct_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_schedule_direct_test_root }));
    b.step("test-sha-schedule-direct", "Prove and natively verify the table-free SHA-256 schedule AIR")
        .dependOn(&sha_schedule_direct_tests.step);
    const sha_feed_direct_test_root = localEntry(b, "sha/tests/sha_feed_direct_proof_test.zig", target, optimize);
    sha_feed_direct_test_root.addImport("stwo_core", core);
    sha_feed_direct_test_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_feed_direct_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_feed_direct_test_root.addImport("s31_sha_provider", sha_provider);
    sha_feed_direct_test_root.addImport("interop_postcard", sha_postcard);
    const sha_feed_direct_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_feed_direct_test_root }));
    b.step("test-sha-feed-direct", "Prove and natively verify the table-free SHA-256 feed-forward AIR")
        .dependOn(&sha_feed_direct_tests.step);
    const sha_caller_stream_test_root = localEntry(b, "sha/tests/sha_caller_stream_proof_test.zig", target, optimize);
    sha_caller_stream_test_root.addImport("stwo_core", core);
    sha_caller_stream_test_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_caller_stream_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_caller_stream_test_root.addImport("s31_sha_provider", sha_provider);
    sha_caller_stream_test_root.addImport("interop_postcard", sha_postcard);
    const sha_caller_stream_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_caller_stream_test_root }));
    b.step("test-sha-caller-stream", "Prove and natively verify the streamed SHA256d caller AIR")
        .dependOn(&sha_caller_stream_tests.step);
    const sha_round_word_logup_test_root = localEntry(b, "sha/air/sha_round_direct_word_logup.zig", target, optimize);
    sha_round_word_logup_test_root.addImport("stwo_core", core);
    sha_round_word_logup_test_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_round_word_logup_test_root.addImport("s31_sha_provider", sha_provider);
    const sha_round_word_logup_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_round_word_logup_test_root }));
    b.step("test-sha-round-word-logup", "Check committed direct SHA round word-bus interactions")
        .dependOn(&sha_round_word_logup_tests.step);
    const sha_round_word_proof_root = localEntry(b, "sha/tests/sha_round_direct_word_proof_test.zig", target, optimize);
    sha_round_word_proof_root.addImport("stwo_core", core);
    sha_round_word_proof_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_round_word_proof_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_round_word_proof_root.addImport("s31_sha_provider", sha_provider);
    sha_round_word_proof_root.addImport("interop_postcard", sha_postcard);
    const sha_round_word_proof_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_round_word_proof_root }));
    b.step("test-sha-round-word-proof", "Prove direct SHA rounds and their committed word lookup in one STARK")
        .dependOn(&sha_round_word_proof_tests.step);
    const sha_round_shift_word_proof_root = localEntry(b, "sha/tests/sha_round_shift_word_proof_test.zig", target, optimize);
    sha_round_shift_word_proof_root.addImport("stwo_core", core);
    sha_round_shift_word_proof_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_round_shift_word_proof_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_round_shift_word_proof_root.addImport("s31_sha_provider", sha_provider);
    sha_round_shift_word_proof_root.addImport("interop_postcard", sha_postcard);
    const sha_round_shift_word_proof_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_round_shift_word_proof_root }));
    b.step("test-sha-round-shift-word-proof", "Prove shift-register SHA rounds and committed word lookup in one STARK")
        .dependOn(&sha_round_shift_word_proof_tests.step);
    const sha_fused_word_proof_root = localEntry(b, "sha/tests/sha_fused_word_proof_test.zig", target, optimize);
    sha_fused_word_proof_root.addImport("stwo_core", core);
    sha_fused_word_proof_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_fused_word_proof_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_fused_word_proof_root.addImport("s31_sha_provider", sha_provider);
    sha_fused_word_proof_root.addImport("interop_postcard", sha_postcard);
    const sha_fused_word_proof_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_fused_word_proof_root }));
    b.step("test-sha-fused-word-proof", "Prove three fused SHA schedules and rounds with committed word boundaries")
        .dependOn(&sha_fused_word_proof_tests.step);
    const sha_schedule_word_proof_root = localEntry(b, "sha/tests/sha_schedule_direct_word_proof_test.zig", target, optimize);
    sha_schedule_word_proof_root.addImport("stwo_core", core);
    sha_schedule_word_proof_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_schedule_word_proof_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_schedule_word_proof_root.addImport("s31_sha_provider", sha_provider);
    sha_schedule_word_proof_root.addImport("interop_postcard", sha_postcard);
    const sha_schedule_word_proof_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_schedule_word_proof_root }));
    b.step("test-sha-schedule-word", "Prove direct SHA schedule and its committed word lookup in one STARK")
        .dependOn(&sha_schedule_word_proof_tests.step);
    const sha_caller_bus_proof_root = localEntry(b, "sha/tests/sha_caller_stream_bus_proof_test.zig", target, optimize);
    sha_caller_bus_proof_root.addImport("stwo_core", core);
    sha_caller_bus_proof_root.addImport("stwo_circuit_frontend", circuit);
    sha_caller_bus_proof_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_caller_bus_proof_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_caller_bus_proof_root.addImport("s31_sha_provider", sha_provider);
    sha_caller_bus_proof_root.addImport("interop_postcard", sha_postcard);
    const sha_caller_bus_proof_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_caller_bus_proof_root }));
    b.step("test-sha-caller-stream-bus", "Prove the streamed SHA caller and its committed Gate/word lookups")
        .dependOn(&sha_caller_bus_proof_tests.step);
    const sha_direct_gate_closure_root = localEntry(b, "sha/tests/sha_direct_gate_closure_test.zig", target, optimize);
    sha_direct_gate_closure_root.addImport("stwo_core", core);
    sha_direct_gate_closure_root.addImport("stwo_circuit_frontend", circuit);
    sha_direct_gate_closure_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_direct_gate_closure_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_direct_gate_closure_root.addImport("s31_sha_provider", sha_provider);
    sha_direct_gate_closure_root.addImport("s31_poseidon_ref", sha_provider);
    const sha_direct_gate_closure_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_direct_gate_closure_root }));
    b.step("test-sha-direct-gate-closure", "Check direct caller Gate lookup against the Bitcoin sparse-wide circuit")
        .dependOn(&sha_direct_gate_closure_tests.step);
    const sha_direct_private_join_root = localEntry(b, "sha/tests/sha_direct_private_join_proof_test.zig", target, optimize);
    sha_direct_private_join_root.addImport("stwo_core", core);
    sha_direct_private_join_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_direct_private_join_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_direct_private_join_root.addImport("stwo_circuit_frontend", circuit);
    sha_direct_private_join_root.addImport("s31_sha_provider", sha_provider);
    sha_direct_private_join_root.addImport("interop_postcard", sha_postcard);
    const sha_direct_private_join_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_direct_private_join_root }));
    b.step("test-sha-direct-private-join", "Prove one private SHA256d header with all direct AIRs and word closure")
        .dependOn(&sha_direct_private_join_tests.step);
    const sha_direct_circuit_root = localEntry(b, "sha/tests/sha_direct_circuit_proof_test.zig", target, optimize);
    sha_direct_circuit_root.addImport("stwo_core", core);
    sha_direct_circuit_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_direct_circuit_root.addImport("stwo_circuit_frontend", circuit);
    sha_direct_circuit_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_direct_circuit_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_direct_circuit_root.addImport("interop_postcard", sha_postcard);
    sha_direct_circuit_root.addImport("s31_air_programs", official_air);
    sha_direct_circuit_root.addImport("s31_sha_provider", sha_provider);
    sha_direct_circuit_root.addImport("s31_poseidon_ref", sha_provider);
    const sha_direct_circuit_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_direct_circuit_root }));
    b.step("test-sha-direct-circuit", "Prove one Bitcoin circuit plus private direct SHA256d in one STARK")
        .dependOn(&sha_direct_circuit_tests.step);
    const sha_shift_private_join_root = localEntry(b, "sha/tests/sha_shift_private_join_proof_test.zig", target, optimize);
    sha_shift_private_join_root.addImport("stwo_core", core);
    sha_shift_private_join_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_shift_private_join_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_shift_private_join_root.addImport("stwo_circuit_frontend", circuit);
    sha_shift_private_join_root.addImport("s31_sha_provider", sha_provider);
    sha_shift_private_join_root.addImport("interop_postcard", sha_postcard);
    const sha_shift_private_join_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_shift_private_join_root }));
    b.step("test-sha-shift-private-join", "Prove one private SHA256d header with shift-register round AIRs")
        .dependOn(&sha_shift_private_join_tests.step);
    const sha_fused_private_join_root = localEntry(b, "sha/tests/sha_fused_private_join_proof_test.zig", target, optimize);
    sha_fused_private_join_root.addImport("stwo_core", core);
    sha_fused_private_join_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_fused_private_join_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_fused_private_join_root.addImport("stwo_circuit_frontend", circuit);
    sha_fused_private_join_root.addImport("s31_sha_provider", sha_provider);
    sha_fused_private_join_root.addImport("interop_postcard", sha_postcard);
    const sha_fused_private_join_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_fused_private_join_root }));
    b.step("test-sha-fused-private-join", "Prove one private SHA256d header with fused schedule and rounds")
        .dependOn(&sha_fused_private_join_tests.step);
    const sha_fused_fold_profile_root = localEntry(b, "sha/config/sha_fused_fold_profile.zig", target, optimize);
    sha_fused_fold_profile_root.addImport("stwo_core", core);
    sha_fused_fold_profile_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_fused_fold_profile_root.addImport("stwo_circuit_frontend", circuit);
    sha_fused_fold_profile_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_fused_fold_profile_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_fused_fold_profile_root.addImport("interop_postcard", sha_postcard);
    sha_fused_fold_profile_root.addImport("s31_air_programs", official_air);
    sha_fused_fold_profile_root.addImport("s31_sha_provider", sha_provider);
    const sha_fused_fold_profile_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_fused_fold_profile_root }));
    b.step("test-sha-fused-fold-profile", "Check the full-circuit fused SHA fold profile and ABI")
        .dependOn(&sha_fused_fold_profile_tests.step);
    const sha_fused_fold_proof_root = localEntry(b, "sha/tests/sha_fused_fold_proof_test.zig", target, optimize);
    sha_fused_fold_proof_root.addImport("stwo_core", core);
    sha_fused_fold_proof_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_fused_fold_proof_root.addImport("stwo_circuit_frontend", circuit);
    sha_fused_fold_proof_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_fused_fold_proof_root.addImport("stwo_circuit_recursion_wire", wire);
    sha_fused_fold_proof_root.addImport("stwo_s31_prototype", frontend);
    sha_fused_fold_proof_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_fused_fold_proof_root.addImport("interop_postcard", sha_postcard);
    sha_fused_fold_proof_root.addImport("s31_air_programs", official_air);
    sha_fused_fold_proof_root.addImport("s31_sha_provider", sha_provider);
    sha_fused_fold_proof_root.addAnonymousImport("s31_air_projection", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") },
    });
    sha_fused_fold_proof_root.addAnonymousImport("s31_bitcoin_fixture", .{
        .root_source_file = b.path("examples/bitcoin/bitcoin_header_link.valid.json"),
    });
    const sha_fused_fold_proof_tests = b.addTest(.{ .root_module = sha_fused_fold_proof_root });
    b.step("check-sha-fused-fold-proof", "Compile the opt-in fused SHA Bitcoin fold integration proof")
        .dependOn(&sha_fused_fold_proof_tests.step);
    b.step("test-sha-fused-fold-proof", "Prove and verify a checkpoint-anchored fused SHA Bitcoin fold")
        .dependOn(&b.addRunArtifact(sha_fused_fold_proof_tests).step);
    const fused_chain_verifier_root = localEntry(b, "bitcoin/tests/bitcoin_fused_chain_verifier_test.zig", target, optimize);
    fused_chain_verifier_root.addImport("stwo_core", core);
    fused_chain_verifier_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    fused_chain_verifier_root.addImport("stwo_circuit_frontend", circuit);
    fused_chain_verifier_root.addImport("stwo_circuit_cpu_integration", cpu);
    fused_chain_verifier_root.addImport("stwo_s31_prototype", frontend);
    fused_chain_verifier_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    fused_chain_verifier_root.addImport("interop_postcard", sha_postcard);
    fused_chain_verifier_root.addImport("s31_air_programs", official_air);
    fused_chain_verifier_root.addImport("s31_sha_provider", sha_provider);
    fused_chain_verifier_root.addAnonymousImport("s31_air_projection", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") },
    });
    const fused_chain_verifier_tests = b.addTest(.{ .root_module = fused_chain_verifier_root });
    b.step("check-bitcoin-fused-chain-verifier", "Compile the sealed one-header fused Bitcoin verifier")
        .dependOn(&fused_chain_verifier_tests.step);
    b.step("test-bitcoin-fused-chain-verifier", "Validate the sealed fused Bitcoin key and statement")
        .dependOn(&b.addRunArtifact(fused_chain_verifier_tests).step);
    const sha_fused_fold_matched_root = localEntry(b, "sha/tests/sha_fused_fold_matched_bench_test.zig", target, optimize);
    sha_fused_fold_matched_root.addImport("stwo_core", core);
    sha_fused_fold_matched_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_fused_fold_matched_root.addImport("stwo_circuit_frontend", circuit);
    sha_fused_fold_matched_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_fused_fold_matched_root.addImport("stwo_s31_prototype", frontend);
    sha_fused_fold_matched_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_fused_fold_matched_root.addImport("interop_postcard", sha_postcard);
    sha_fused_fold_matched_root.addImport("s31_air_programs", official_air);
    sha_fused_fold_matched_root.addImport("s31_sha_provider", sha_provider);
    sha_fused_fold_matched_root.addAnonymousImport("s31_air_projection", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") },
    });
    sha_fused_fold_matched_root.addAnonymousImport("s31_bitcoin_fixture", .{
        .root_source_file = b.path("examples/bitcoin/bitcoin_header_link.valid.json"),
    });
    const sha_fused_fold_matched_tests = b.addTest(.{ .root_module = sha_fused_fold_matched_root });
    b.step("check-sha-fused-fold-matched-bench", "Compile the matched generic versus fused fold benchmark")
        .dependOn(&sha_fused_fold_matched_tests.step);
    b.step("test-sha-fused-fold-matched-bench", "Compare generic and fused SHA Bitcoin fold proofs")
        .dependOn(&b.addRunArtifact(sha_fused_fold_matched_tests).step);
    const sha_shift_circuit_root = localEntry(b, "sha/tests/sha_shift_circuit_proof_test.zig", target, optimize);
    sha_shift_circuit_root.addImport("stwo_core", core);
    sha_shift_circuit_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_shift_circuit_root.addImport("stwo_circuit_frontend", circuit);
    sha_shift_circuit_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_shift_circuit_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_shift_circuit_root.addImport("interop_postcard", sha_postcard);
    sha_shift_circuit_root.addImport("s31_air_programs", official_air);
    sha_shift_circuit_root.addImport("s31_sha_provider", sha_provider);
    sha_shift_circuit_root.addImport("s31_poseidon_ref", sha_provider);
    const sha_shift_circuit_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_shift_circuit_root }));
    b.step("test-sha-shift-circuit", "Prove one Bitcoin circuit plus shift-register SHA256d in one STARK")
        .dependOn(&sha_shift_circuit_tests.step);
    const sha_fused_circuit_root = localEntry(b, "sha/tests/sha_fused_circuit_proof_test.zig", target, optimize);
    sha_fused_circuit_root.addImport("stwo_core", core);
    sha_fused_circuit_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_fused_circuit_root.addImport("stwo_circuit_frontend", circuit);
    sha_fused_circuit_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_fused_circuit_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_fused_circuit_root.addImport("interop_postcard", sha_postcard);
    sha_fused_circuit_root.addImport("s31_air_programs", official_air);
    sha_fused_circuit_root.addImport("s31_sha_provider", sha_provider);
    sha_fused_circuit_root.addImport("s31_poseidon_ref", sha_provider);
    const sha_fused_circuit_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_fused_circuit_root }));
    b.step("test-sha-fused-circuit", "Prove one Bitcoin circuit plus fused SHA256d in one STARK")
        .dependOn(&sha_fused_circuit_tests.step);
    const sha_fused_bench_root = localEntry(b, "sha/tests/sha_fused_vs_shift_bench_test.zig", target, optimize);
    sha_fused_bench_root.addImport("stwo_core", core);
    sha_fused_bench_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_fused_bench_root.addImport("stwo_circuit_frontend", circuit);
    sha_fused_bench_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_fused_bench_root.addImport("stwo_circuit_recursion_wire", wire);
    sha_fused_bench_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    sha_fused_bench_root.addImport("interop_postcard", sha_postcard);
    sha_fused_bench_root.addImport("s31_air_programs", official_air);
    sha_fused_bench_root.addImport("s31_sha_provider", sha_provider);
    sha_fused_bench_root.addImport("s31_poseidon_ref", sha_provider);
    const sha_fused_bench_exe = b.addExecutable(.{ .name = "s31-sha-fused-vs-shift-bench", .root_module = sha_fused_bench_root });
    const sha_fused_bench_install = b.addInstallArtifact(sha_fused_bench_exe, .{});
    b.step("bench-sha-fused-vs-shift", "Build production-mode fused versus shift SHA Bitcoin benchmark")
        .dependOn(&sha_fused_bench_install.step);
    const bitcoin_matched_bench_root = localEntry(b, "bitcoin/tests/bitcoin_generic_vs_sha_shift_bench_test.zig", target, optimize);
    bitcoin_matched_bench_root.addImport("stwo_core", core);
    bitcoin_matched_bench_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    bitcoin_matched_bench_root.addImport("stwo_circuit_frontend", circuit);
    bitcoin_matched_bench_root.addImport("stwo_circuit_cpu_integration", cpu);
    bitcoin_matched_bench_root.addImport("stwo_circuit_recursion_wire", wire);
    bitcoin_matched_bench_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    bitcoin_matched_bench_root.addImport("interop_postcard", sha_postcard);
    bitcoin_matched_bench_root.addImport("s31_air_programs", official_air);
    bitcoin_matched_bench_root.addImport("s31_sha_provider", sha_provider);
    bitcoin_matched_bench_root.addImport("s31_poseidon_ref", sha_provider);
    const bitcoin_matched_bench_tests = b.addRunArtifact(b.addTest(.{ .root_module = bitcoin_matched_bench_root }));
    b.step("test-bitcoin-generic-vs-sha-shift", "Compare generic and shift-SHA Bitcoin proof timing in one harness")
        .dependOn(&bitcoin_matched_bench_tests.step);
    const bitcoin_matched_bench_exe_root = localEntry(b, "bitcoin/tests/bitcoin_generic_vs_sha_shift_bench_test.zig", target, optimize);
    bitcoin_matched_bench_exe_root.addImport("stwo_core", core);
    bitcoin_matched_bench_exe_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    bitcoin_matched_bench_exe_root.addImport("stwo_circuit_frontend", circuit);
    bitcoin_matched_bench_exe_root.addImport("stwo_circuit_cpu_integration", cpu);
    bitcoin_matched_bench_exe_root.addImport("stwo_circuit_recursion_wire", wire);
    bitcoin_matched_bench_exe_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    bitcoin_matched_bench_exe_root.addImport("interop_postcard", sha_postcard);
    bitcoin_matched_bench_exe_root.addImport("s31_air_programs", official_air);
    bitcoin_matched_bench_exe_root.addImport("s31_sha_provider", sha_provider);
    bitcoin_matched_bench_exe_root.addImport("s31_poseidon_ref", sha_provider);
    const bitcoin_matched_bench_exe = b.addExecutable(.{ .name = "s31-bitcoin-generic-vs-sha-shift-bench", .root_module = bitcoin_matched_bench_exe_root });
    const bitcoin_matched_bench_install = b.addInstallArtifact(bitcoin_matched_bench_exe, .{});
    b.step("bitcoin-generic-vs-sha-shift-bench", "Build production-mode generic and shift-SHA Bitcoin benchmark")
        .dependOn(&bitcoin_matched_bench_install.step);
    const bitcoin_multi_witness_root = localEntry(b, "bitcoin/tests/bitcoin_multi_witness_bench.zig", target, optimize);
    bitcoin_multi_witness_root.addImport("stwo_core", core);
    bitcoin_multi_witness_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    bitcoin_multi_witness_root.addImport("stwo_circuit_frontend", circuit);
    bitcoin_multi_witness_root.addImport("stwo_circuit_cpu_integration", cpu);
    bitcoin_multi_witness_root.addImport("stwo_circuit_recursion_wire", wire);
    bitcoin_multi_witness_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    bitcoin_multi_witness_root.addImport("interop_postcard", sha_postcard);
    bitcoin_multi_witness_root.addImport("s31_air_programs", official_air);
    bitcoin_multi_witness_root.addImport("s31_sha_provider", sha_provider);
    bitcoin_multi_witness_root.addImport("s31_poseidon_ref", sha_provider);
    const bitcoin_multi_witness_exe = b.addExecutable(.{ .name = "s31-bitcoin-multi-witness-bench", .root_module = bitcoin_multi_witness_root });
    b.step("bench-bitcoin-multi-witness", "Build production-mode matched Bitcoin proof benchmark across distinct headers")
        .dependOn(&b.addInstallArtifact(bitcoin_multi_witness_exe, .{}).step);
    const sha_feed_word_proof_root = localEntry(b, "sha/tests/sha_feed_direct_word_proof_test.zig", target, optimize);
    sha_feed_word_proof_root.addImport("stwo_core", core);
    sha_feed_word_proof_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_feed_word_proof_root.addImport("stwo_circuit_cpu_integration", cpu);
    sha_feed_word_proof_root.addImport("s31_sha_provider", sha_provider);
    sha_feed_word_proof_root.addImport("interop_postcard", sha_postcard);
    const sha_feed_word_proof_tests = b.addRunArtifact(b.addTest(.{ .root_module = sha_feed_word_proof_root }));
    b.step("test-sha-feed-word", "Prove SHA feed-forward and its committed word lookup in one STARK")
        .dependOn(&sha_feed_word_proof_tests.step);
    const retarget_proof_test_root = localEntry(b, "bitcoin/tests/bitcoin_retarget_proof_test.zig", target, optimize);
    retarget_proof_test_root.addImport("stwo_core", core);
    retarget_proof_test_root.addImport("stwo_circuit_frontend", circuit);
    retarget_proof_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    retarget_proof_test_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    retarget_proof_test_root.addImport("interop_postcard", sha_postcard);
    retarget_proof_test_root.addImport("s31_air_programs", official_air);
    const retarget_proof_tests = b.addRunArtifact(b.addTest(.{ .root_module = retarget_proof_test_root }));
    b.step("test-bitcoin-retarget-proof", "Prove and natively verify the first Bitcoin retarget relation")
        .dependOn(&retarget_proof_tests.step);
    anchor_proof_test_root.addAnonymousImport("s31_bitcoin_fixture", .{
        .root_source_file = b.path("examples/bitcoin/bitcoin_header_link.valid.json"),
    });
    anchor_proof_test_root.addAnonymousImport("s31_bitcoin_block2_fixture", .{
        .root_source_file = b.path("examples/bitcoin/bitcoin_block2_header.valid.json"),
    });
    const anchor_proof_tests = b.addRunArtifact(b.addTest(.{
        .root_module = anchor_proof_test_root,
        .filters = &.{"Bitcoin checkpoint anchor proves and verifies under the fold child layout"},
    }));
    b.step("test-bitcoin-anchor-proof", "Prove and natively verify the full-layout Bitcoin checkpoint anchor")
        .dependOn(&anchor_proof_tests.step);
    const chain_fold_proof_tests = b.addRunArtifact(b.addTest(.{
        .root_module = anchor_proof_test_root,
        .filters = &.{"Bitcoin chain fold proves two changing headers over a verified checkpoint anchor"},
    }));
    b.step("test-bitcoin-chain-fold-proof", "Prove and natively verify a Bitcoin header update inside a recursive fold")
        .dependOn(&chain_fold_proof_tests.step);
    const retarget_chain_proof_tests = b.addRunArtifact(b.addTest(.{
        .root_module = anchor_proof_test_root,
        .filters = &.{"first-retarget fold profile proves and verifies a genesis-anchored header"},
    }));
    b.step("test-bitcoin-retarget-fold-proof", "Prove and natively verify the first-retarget fold profile at step zero")
        .dependOn(&retarget_chain_proof_tests.step);
    const retarget_chain_key_root = localEntry(b, "bitcoin/verification/bitcoin_chain_retarget_verifier.zig", target, optimize);
    retarget_chain_key_root.addImport("stwo_core", core);
    retarget_chain_key_root.addImport("stwo_circuit_frontend", circuit);
    retarget_chain_key_root.addImport("stwo_circuit_cpu_integration", cpu);
    retarget_chain_key_root.addImport("stwo_s31_prototype", frontend);
    retarget_chain_key_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    retarget_chain_key_root.addImport("interop_postcard", sha_postcard);
    retarget_chain_key_root.addImport("s31_air_programs", official_air);
    retarget_chain_key_root.addAnonymousImport("s31_air_projection", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") },
    });
    const retarget_chain_key_tests = b.addRunArtifact(b.addTest(.{ .root_module = retarget_chain_key_root }));
    b.step("test-bitcoin-retarget-fold-key", "Derive and validate the distinct first-retarget recursive fold key")
        .dependOn(&retarget_chain_key_tests.step);
    const bitcoin_cli_root = localEntry(b, "bitcoin/cli/bitcoin_chain_cli.zig", target, optimize);
    bitcoin_cli_root.addImport("stwo_core", core);
    bitcoin_cli_root.addImport("stwo_circuit_frontend", circuit);
    bitcoin_cli_root.addImport("stwo_circuit_cpu_integration", cpu);
    bitcoin_cli_root.addImport("stwo_s31_prototype", frontend);
    bitcoin_cli_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
    bitcoin_cli_root.addImport("interop_postcard", sha_postcard);
    bitcoin_cli_root.addImport("s31_air_programs", official_air);
    bitcoin_cli_root.addAnonymousImport("s31_air_projection", .{
        .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") },
    });
    const bitcoin_cli = b.addExecutable(.{ .name = "s31-bitcoin-chain", .root_module = bitcoin_cli_root });
    b.step("bitcoin-chain-cli", "Build the standalone Bitcoin chain key and native verifier CLI")
        .dependOn(&b.addInstallArtifact(bitcoin_cli, .{}).step);
    const fold_test_root = localEntry(b, "recursion/state_fold.zig", target, optimize);
    fold_test_root.addImport("stwo_s31_prototype", frontend);
    fold_test_root.addImport("stwo_core", core);
    fold_test_root.addImport("stwo_circuit_frontend", circuit);
    fold_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    const fold_tests = b.addRunArtifact(b.addTest(.{
        .root_module = fold_test_root,
        .filters = &.{ "state-fold counter spans u16 carry and u32 bounds", "state-fold source step body matches constrained circuit across mixed programs", "state-fold digest binds all 32 counter bits in circuit" },
    }));
    test_step.dependOn(&fold_tests.step);
    const fixed_fold_test_root = localEntry(b, "recursion/fixed_fold.zig", target, optimize);
    fixed_fold_test_root.addImport("stwo_core", core);
    fixed_fold_test_root.addImport("stwo_circuit_frontend", circuit);
    fixed_fold_test_root.addImport("stwo_circuit_cpu_integration", cpu);
    const fixed_fold_tests = b.addRunArtifact(b.addTest(.{
        .root_module = fixed_fold_test_root,
        .filters = &.{"fixed-fold digest binds the full u32 counter"},
    }));
    test_step.dependOn(&fixed_fold_tests.step);

    const sha_batch_root = b.createModule(.{
        .root_source_file = b.path("../riscv/sha256_batch_test_root.zig"),
        .target = target,
        .optimize = optimize,
    });
    sha_batch_root.addImport("stwo_core", core);
    sha_batch_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
    sha_batch_root.addImport("stwo_cpu_backend", cpu.import_table.get("stwo_cpu_backend") orelse @panic("missing CPU backend"));
    const sha_batch_tests = b.addRunArtifact(b.addTest(.{
        .root_module = sha_batch_root,
        .filters = &.{ "SHA canonical compression STARK", "six linked SHA compression calls" },
    }));
    b.step("test-sha-batch", "Prove and verify a six-call SHA256d AIR batch").dependOn(&sha_batch_tests.step);

    if (mixed_lowering and (source_version == 1 or
        (source_version == 2 and std.mem.eql(u8, lowering, "direct-mixed-general"))))
    {
        const mixed_four = std.mem.eql(u8, lowering, "direct-mixed4");
        const mixed_general = std.mem.eql(u8, lowering, "direct-mixed-general");
        const mixed_prover_root = localEntry(b, if (mixed_general) "runtime/mixed_boundary/general_prover_main.zig" else if (mixed_four) "runtime/mixed_boundary/n4_prover_main.zig" else "runtime/mixed_boundary/mixed_prover_main.zig", target, optimize);
        const mixed_verifier_root = localEntry(b, if (mixed_general) "runtime/mixed_boundary/general_verifier_main.zig" else if (mixed_four) "runtime/mixed_boundary/n4_verifier_main.zig" else "runtime/mixed_boundary/mixed_verifier_main.zig", target, optimize);
        const mixed_manifest_root = localEntry(b, if (mixed_general) "runtime/mixed_boundary/general_manifest_main.zig" else if (mixed_four) "runtime/mixed_boundary/n4_manifest_main.zig" else "runtime/mixed_boundary/mixed_manifest_main.zig", target, optimize);
        const mixed_auditor_root = localEntry(b, "runtime/mixed_boundary/general_trace_audit_main.zig", target, optimize);
        for ([_]*std.Build.Module{ mixed_prover_root, mixed_verifier_root, mixed_manifest_root, mixed_auditor_root }) |root| {
            root.addImport("stwo_core", core);
            root.addImport("stwo_circuit_frontend", circuit);
            root.addImport("stwo_circuit_cpu_integration", cpu);
            root.addImport("stwo_circuit_recursion_wire", wire);
            root.addImport("stwo_s31_prototype", frontend);
            root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
            root.addImport("interop_postcard", sha_postcard);
            root.addImport("s31_air_programs", official_air);
            root.addImport("s31_sha_provider", sha_provider);
            root.addImport("s31_poseidon_ref", sha_provider);
            root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
            root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
            root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
            root.addAnonymousImport("s31_many_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_many_boundary.zig") } });
            root.addAnonymousImport("s31_many_preflight_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig") } });
            root.addAnonymousImport("s31_many_direct_circuit_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig") } });
            root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
            root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
            root.addAnonymousImport("s31_tagged_many_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_chip.zig") } });
            root.addAnonymousImport("s31_tagged_many_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_bridge.zig") } });
            root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
        }
        const profile_name = if (mixed_general) "mixed-general" else if (mixed_four) "mixed4" else "mixed";
        const mixed_prover = b.addExecutable(.{ .name = b.fmt("s31-{s}-{s}-prover", .{ program_name, profile_name }), .root_module = mixed_prover_root });
        const mixed_verifier = b.addExecutable(.{ .name = b.fmt("s31-{s}-{s}-native-verifier", .{ program_name, profile_name }), .root_module = mixed_verifier_root });
        const mixed_manifest = b.addExecutable(.{ .name = b.fmt("s31-{s}-{s}-manifest", .{ program_name, profile_name }), .root_module = mixed_manifest_root });
        const mixed_auditor = if (mixed_general)
            b.addExecutable(.{ .name = b.fmt("s31-{s}-{s}-trace-auditor", .{ program_name, profile_name }), .root_module = mixed_auditor_root })
        else
            null;
        const mixed_source_check = b.addRunArtifact(mixed_manifest);
        mixed_source_check.addArg("--check");
        mixed_prover.step.dependOn(&mixed_source_check.step);
        mixed_verifier.step.dependOn(&mixed_source_check.step);
        if (mixed_auditor) |auditor| auditor.step.dependOn(&mixed_source_check.step);
        b.installArtifact(mixed_prover);
        b.installArtifact(mixed_verifier);
        b.installArtifact(mixed_manifest);
        if (mixed_auditor) |auditor| b.installArtifact(auditor);
        b.getInstallStep().dependOn(&mixed_source_check.step);
        const mixed_programs = b.step("mixed-programs", "Build experimental source-pinned mixed prover, verifier, and component inspector for the selected profile");
        mixed_programs.dependOn(&mixed_prover.step);
        mixed_programs.dependOn(&mixed_verifier.step);
        mixed_programs.dependOn(&mixed_manifest.step);
        if (mixed_auditor) |auditor| mixed_programs.dependOn(&auditor.step);
        mixed_programs.dependOn(&mixed_source_check.step);
        return;
    }
    if (source_version == 1 and std.mem.eql(u8, lowering, "direct-many")) {
        const many_prover_root = localEntry(b, "runtime/many_prover_main.zig", target, optimize);
        const many_verifier_root = localEntry(b, "runtime/many_verifier_main.zig", target, optimize);
        const many_manifest_root = localEntry(b, "runtime/many_manifest_main.zig", target, optimize);
        for ([_]*std.Build.Module{ many_prover_root, many_verifier_root, many_manifest_root }) |root| {
            root.addImport("stwo_core", core);
            root.addImport("stwo_circuit_frontend", circuit);
            root.addImport("stwo_circuit_cpu_integration", cpu);
            root.addImport("stwo_s31_prototype", frontend);
            root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
            root.addImport("interop_postcard", sha_postcard);
            root.addImport("s31_air_programs", official_air);
            root.addImport("s31_sha_provider", sha_provider);
            root.addImport("s31_poseidon_ref", sha_provider);
            root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
            root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
            root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
            root.addAnonymousImport("s31_many_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_many_boundary.zig") } });
            root.addAnonymousImport("s31_many_preflight_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig") } });
            root.addAnonymousImport("s31_many_direct_circuit_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/frontends/circuit/common/direct_arithmetic.zig") } });
            root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
            root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
            root.addAnonymousImport("s31_tagged_many_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_chip.zig") } });
            root.addAnonymousImport("s31_tagged_many_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_many_bridge.zig") } });
            root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
        }
        const many_prover = b.addExecutable(.{ .name = b.fmt("s31-{s}-many-prover", .{program_name}), .root_module = many_prover_root });
        b.installArtifact(many_prover);
        const many_verifier = b.addExecutable(.{ .name = b.fmt("s31-{s}-many-native-verifier", .{program_name}), .root_module = many_verifier_root });
        b.installArtifact(many_verifier);
        const many_manifest = b.addExecutable(.{ .name = b.fmt("s31-{s}-many-manifest", .{program_name}), .root_module = many_manifest_root });
        b.installArtifact(many_manifest);
        const many_programs = b.step("many-programs", "Build experimental source-pinned V4 bounded prover, verifier, and component inspector");
        many_programs.dependOn(&many_prover.step);
        many_programs.dependOn(&many_verifier.step);
        many_programs.dependOn(&many_manifest.step);
        return;
    }
    if (source_version == 1 and std.mem.eql(u8, lowering, "direct-pair")) {
        const pair_prover_root = localEntry(b, "runtime/pair_prover_main.zig", target, optimize);
        pair_prover_root.addImport("stwo_core", core);
        pair_prover_root.addImport("stwo_circuit_frontend", circuit);
        pair_prover_root.addImport("stwo_circuit_cpu_integration", cpu);
        pair_prover_root.addImport("stwo_s31_prototype", frontend);
        pair_prover_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
        pair_prover_root.addImport("interop_postcard", sha_postcard);
        pair_prover_root.addImport("s31_air_programs", official_air);
        pair_prover_root.addImport("s31_sha_provider", sha_provider);
        pair_prover_root.addImport("s31_poseidon_ref", sha_provider);
        pair_prover_root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
        pair_prover_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
        pair_prover_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
        pair_prover_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
        pair_prover_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
        pair_prover_root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
        const pair_prover = b.addExecutable(.{ .name = b.fmt("s31-{s}-pair-prover", .{program_name}), .root_module = pair_prover_root });
        b.installArtifact(pair_prover);
        const pair_verifier_root = localEntry(b, "runtime/pair_verifier_main.zig", target, optimize);
        pair_verifier_root.addImport("stwo_core", core);
        pair_verifier_root.addImport("stwo_circuit_frontend", circuit);
        pair_verifier_root.addImport("stwo_circuit_cpu_integration", cpu);
        pair_verifier_root.addImport("stwo_s31_prototype", frontend);
        pair_verifier_root.addImport("stwo_cairo_frontend", cpu.import_table.get("stwo_cairo_frontend") orelse @panic("missing Cairo frontend"));
        pair_verifier_root.addImport("interop_postcard", sha_postcard);
        pair_verifier_root.addImport("s31_air_programs", official_air);
        pair_verifier_root.addImport("s31_sha_provider", sha_provider);
        pair_verifier_root.addImport("s31_poseidon_ref", sha_provider);
        pair_verifier_root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
        pair_verifier_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
        pair_verifier_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
        pair_verifier_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
        pair_verifier_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
        pair_verifier_root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
        const pair_verifier = b.addExecutable(.{ .name = b.fmt("s31-{s}-pair-native-verifier", .{program_name}), .root_module = pair_verifier_root });
        b.installArtifact(pair_verifier);
        const pair_programs = b.step("pair-programs", "Build the experimental source-pinned two-call prover and verifier");
        pair_programs.dependOn(&pair_prover.step);
        pair_programs.dependOn(&pair_verifier.step);
        return;
    }
    if (source_version == 1 or (source_version == 2 and std.mem.eql(u8, lowering, "direct-gate"))) {
        const cairo = cpu.import_table.get("stwo_cairo_frontend") orelse @panic("circuit CPU module is missing Cairo AIR runtime");
        const key_asset: std.Build.LazyPath = if (b.option([]const u8, "s31-key", "Absolute path to the sealed verification key")) |path|
            .{ .cwd_relative = path }
        else
            b.path("examples/keys/placeholder-verification-key.json");
        const recursive_key_asset: std.Build.LazyPath = if (b.option([]const u8, "s31-recursive-key", "Absolute path to the sealed recursive verification key")) |path|
            .{ .cwd_relative = path }
        else
            b.path("examples/keys/placeholder-recursive-key.json");
        const recursive_next_key_asset: std.Build.LazyPath = if (b.option([]const u8, "s31-recursive-next-key", "Absolute path to the sealed second-level recursive verification key")) |path|
            .{ .cwd_relative = path }
        else
            b.path("examples/keys/placeholder-recursive-key.json");
        const fold_key_asset: std.Build.LazyPath = if (b.option([]const u8, "s31-fold-key", "Absolute path to the sealed fixed-fold verification key")) |path|
            .{ .cwd_relative = path }
        else
            b.path("examples/keys/placeholder-recursive-key.json");
        const state_fold_key_asset: std.Build.LazyPath = if (b.option([]const u8, "s31-state-fold-key", "Absolute path to the sealed state-transition fold verification key")) |path|
            .{ .cwd_relative = path }
        else
            b.path("examples/keys/placeholder-recursive-key.json");
        const prover_root = localEntry(b, "runtime/mvp_runtime.zig", target, optimize);
        prover_root.addImport("stwo_s31_prototype", frontend);
        prover_root.addImport("stwo_core", core);
        prover_root.addImport("stwo_circuit_frontend", circuit);
        prover_root.addImport("stwo_circuit_cpu_integration", cpu);
        prover_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
        prover_root.addImport("s31_sha_provider", sha_provider);
        prover_root.addImport("stwo_cairo_frontend", cairo);
        prover_root.addImport("interop_postcard", sha_postcard);
        prover_root.addImport("stwo_circuit_recursion_wire", wire);
        prover_root.addOptions("s31_options", s31_options);
        prover_root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
        const projection_asset: std.Build.LazyPath = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") };
        prover_root.addAnonymousImport("s31_air_projection", .{ .root_source_file = projection_asset });
        prover_root.addImport("s31_air_programs", official_air);
        prover_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
        prover_root.addAnonymousImport("s31_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_boundary_bridge.zig") } });
        prover_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
        prover_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
        prover_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
        prover_root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
        prover_root.addAnonymousImport("s31_verification_key", .{ .root_source_file = key_asset });
        prover_root.addAnonymousImport("s31_recursive_key", .{ .root_source_file = recursive_key_asset });
        prover_root.addAnonymousImport("s31_recursive_next_key", .{ .root_source_file = recursive_next_key_asset });
        prover_root.addAnonymousImport("s31_fold_key", .{ .root_source_file = fold_key_asset });
        prover_root.addAnonymousImport("s31_state_fold_key", .{ .root_source_file = state_fold_key_asset });
        const prover_exe = b.addExecutable(.{ .name = b.fmt("s31-{s}-prover", .{program_name}), .root_module = prover_root });
        b.installArtifact(prover_exe);

        const native_root = localEntry(b, "runtime/mvp_verifier_main.zig", target, optimize);
        native_root.addImport("stwo_s31_prototype", frontend);
        native_root.addImport("stwo_core", core);
        native_root.addImport("stwo_circuit_frontend", circuit);
        native_root.addImport("stwo_circuit_cpu_integration", cpu);
        native_root.addImport("stwo_prover_engine", cpu.import_table.get("stwo_prover_engine") orelse @panic("missing prover engine"));
        native_root.addImport("s31_sha_provider", sha_provider);
        native_root.addImport("stwo_cairo_frontend", cairo);
        native_root.addImport("interop_postcard", sha_postcard);
        native_root.addImport("stwo_circuit_recursion_wire", wire);
        native_root.addOptions("s31_options", s31_options);
        native_root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
        native_root.addAnonymousImport("s31_air_projection", .{ .root_source_file = projection_asset });
        native_root.addImport("s31_air_programs", official_air);
        native_root.addAnonymousImport("s31_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/repeated_step_chip.zig") } });
        native_root.addAnonymousImport("s31_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_boundary_bridge.zig") } });
        native_root.addAnonymousImport("s31_pair_boundary_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/private_pair_boundary.zig") } });
        native_root.addAnonymousImport("s31_tagged_pair_chip_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig") } });
        native_root.addAnonymousImport("s31_tagged_pair_bridge_air_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_bridge.zig") } });
        native_root.addAnonymousImport("s31_pair_proof_source", .{ .root_source_file = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/src/integrations/circuit_cpu/direct_pair_arithmetic.zig") } });
        native_root.addAnonymousImport("s31_verification_key", .{ .root_source_file = key_asset });
        native_root.addAnonymousImport("s31_recursive_key", .{ .root_source_file = recursive_key_asset });
        native_root.addAnonymousImport("s31_recursive_next_key", .{ .root_source_file = recursive_next_key_asset });
        native_root.addAnonymousImport("s31_fold_key", .{ .root_source_file = fold_key_asset });
        native_root.addAnonymousImport("s31_state_fold_key", .{ .root_source_file = state_fold_key_asset });
        const native_exe = b.addExecutable(.{ .name = b.fmt("s31-{s}-native-verifier", .{program_name}), .root_module = native_root });
        b.installArtifact(native_exe);
        const run = b.addRunArtifact(prover_exe);
        if (b.args) |args| run.addArgs(args);
        b.step("program", "Run the S31 v1 program compiler/prover").dependOn(&run.step);
        return;
    }
    if (source_version != 0) @panic("unsupported S31 source version");

    const showcase_root = localEntry(b, "runtime/showcase.zig", target, optimize);
    showcase_root.addImport("stwo_s31_prototype", frontend);
    showcase_root.addImport("stwo_core", core);
    showcase_root.addImport("stwo_circuit_frontend", circuit);
    showcase_root.addImport("stwo_circuit_cpu_integration", cpu);
    showcase_root.addImport("stwo_circuit_recursion_wire", wire);
    showcase_root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
    const projection_asset: std.Build.LazyPath = .{ .cwd_relative = b.pathFromRoot("../../../deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin") };
    showcase_root.addAnonymousImport("s31_air_projection", .{ .root_source_file = projection_asset });
    showcase_root.addImport("s31_air_programs", official_air);
    const executable = b.addExecutable(.{ .name = "s31-showcase", .root_module = showcase_root });
    b.installArtifact(executable);

    const verifier_root = localEntry(b, "runtime/verifier_main.zig", target, optimize);
    verifier_root.addImport("stwo_s31_prototype", frontend);
    verifier_root.addImport("stwo_core", core);
    verifier_root.addImport("stwo_circuit_frontend", circuit);
    verifier_root.addImport("stwo_circuit_cpu_integration", cpu);
    verifier_root.addImport("stwo_circuit_recursion_wire", wire);
    verifier_root.addAnonymousImport("s31_program_source", .{ .root_source_file = source_asset });
    verifier_root.addAnonymousImport("s31_air_projection", .{ .root_source_file = projection_asset });
    verifier_root.addImport("s31_air_programs", official_air);
    const verifier = b.addExecutable(.{ .name = b.fmt("s31-{s}-verifier", .{program_name}), .root_module = verifier_root });
    b.installArtifact(verifier);

    const showcase = b.addRunArtifact(executable);
    showcase.setCwd(.{ .cwd_relative = b.pathFromRoot("../../..") });
    if (b.args) |args| showcase.addArgs(args);
    const showcase_step = b.step("showcase", "Prove and natively verify the S31 affine-four example");
    showcase_step.dependOn(&showcase.step);
    showcase_step.dependOn(b.getInstallStep());
}

/// Keep the Zig module root at S31 while individual test and executable
/// sources live in their domain directories. This permits imports across
/// sibling directories without widening module access outside S31.
fn localEntry(b: *std.Build, source: []const u8, target: std.Build.ResolvedTarget, optimize: std.builtin.OptimizeMode) *std.Build.Module {
    return b.createModule(.{
        .root_source_file = b.path(b.fmt("entry/{s}", .{std.fs.path.basename(source)})),
        .target = target,
        .optimize = optimize,
    });
}
