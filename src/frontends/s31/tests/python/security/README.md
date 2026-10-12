# Package security tests

`test_package_trust.py` checks the production external-pin admission path. Its
small fixture isolates the pin gate from package construction, so a changed
artifact, missing text pin, or path alias must fail before package validation
or native verifier execution. Full generated-package consistency is exercised
by the package acceptance and security controls elsewhere in this repository.

`test_unpinned_verification.py` and `test_recursive_verification_snapshot.py`
check that ordinary, recursive, and fold verification execute the exact
package copy admitted by Python even when the original package changes.
The fold test also checks that reported checkpoint continuity comes from the
same bounded proof and statement bytes passed to the native verifier.
