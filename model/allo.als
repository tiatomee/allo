// SPDX-FileCopyrightText: 2021 The allo developers
//
// SPDX-License-Identifier: AGPL-3.0-only

one sig Manifest {
	dependencies: some PackageVersion,
}

one sig ManifestLock {
	final_dependencies: some PackageVersion,
}




sig ModuleName {}

sig Package {
	versions: some PackageVersion,
}

sig PackageVersion {
	compatible_with: disj lone PackageVersion,
	modules: some ModuleName,
	depends_on: set PackageVersion,
}

//
// Some things assumed always true or inherent to the system
//

fact "every package version must belong to one package" {
	all v: PackageVersion |
		#v.~versions = 1
}


// Semver doesn't cover cross-package version compatibility
fact "package cannot be compatible with other package" {
	all v: PackageVersion |
		all c: v.^compatible_with |
			c.~versions = v.~versions and #c.~versions = 1
}

// e.g 1.1 is compatible with 1.0 and 1.2 is compatible with 1.1
fact "only one package can be compatible with a package" {
	all v: PackageVersion |
		#v.~compatible_with <= 1
}


/*
// This seemed sensible, but there might be Package.Internal.{A, B, ...}
// modules that *can* be removed
fact "compatible packages must not remove modules" {
	all v: PackageVersion |
		all vi: v.^compatible_with |
			vi.modules in v.modules
}
*/



pred packageValid[p: Package] {
	all v: p.versions {
		// does not depend on itself
		v not in v.^depends_on
		// is not compatible with itself
		v not in v.^compatible_with

		// does not depend on a package that's in its comp set
		no d: v.^depends_on | d in v.^compatible_with
	}
}


pred manifestValid[m: Manifest] {
	all a, b: m.dependencies |
		not (a = b) implies
			(a.~versions = b.~versions) implies
				a not in b.^compatible_with and b not in a.^compatible_with
}

fun latestVersions[ps: set PackageVersion] : set PackageVersion {
	ps.*~compatible_with & { x: PackageVersion | #x.~compatible_with = 0 }
}

pred lockDescribesManifest[m: Manifest, l: ManifestLock] {

	// all dependencies need to be in the lock file
	latestVersions[m.dependencies] in l.final_dependencies

	// none of the final dependencies have "never" versions
	// conceptually, a pinned version is a duplicate version with a
	// restricted compatibility chain
	all v: l.final_dependencies |
		#v.~compatible_with = 0

	// all dependencies from required packages are in the lock file
	latestVersions[latestVersions[m.dependencies].^depends_on] in l.final_dependencies


	// all dependencies in the lock file need to in the dependency chain
	// of the packages in the manifest
	all v: l.final_dependencies |
		v in latestVersions[m.dependencies] or
		v in latestVersions[latestVersions[m.dependencies].^depends_on]
}

pred packagesDontShareModules[vs: set PackageVersion] {
	all m: ModuleName {
		#(m.~modules & vs) <= 1
	}
}

pred systemValid {
	all p: Package | packageValid[p]

	all m: Manifest | manifestValid[m]

	all m: Manifest, l: ManifestLock | lockDescribesManifest[m, l]
	
	all l: ManifestLock | packagesDontShareModules[l.final_dependencies]
}


assert no_more_deps_than_final_deps {
	systemValid implies

	all m: Manifest, l: ManifestLock |
		#m.dependencies <= #l.final_dependencies
}

check no_more_deps_than_final_deps

assert every_final_dep_comes_from_deps {
	systemValid implies

	all m: Manifest, l: ManifestLock |
		all v: l.final_dependencies |
			v in latestVersions[m.dependencies] or
			v in latestVersions[latestVersions[m.dependencies].*depends_on]
}

check every_final_dep_comes_from_deps

run { systemValid and #final_dependencies >= 3 } for 4 but exactly 2 Package, 5 ModuleName, 4 PackageVersion
