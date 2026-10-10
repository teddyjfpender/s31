# Package security tests

`test_package_trust.py` checks the production external-pin admission path. Its
small fixture isolates the pin gate from package construction, so a changed
artifact, missing text pin, or path alias must fail before package validation
or native verifier execution. Full generated-package consistency is exercised
by the package acceptance and security controls elsewhere in this repository.
