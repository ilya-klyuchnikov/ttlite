lazy val commonSettings = Seq(
  scalaVersion := "3.0.0",
  organization := "ttlite",
  version := "0.5-SNAPSHOT",
  scalacOptions ++= Seq("-deprecation", "-feature"),
  run / baseDirectory := (ThisBuild / baseDirectory).value,
  Test / testOptions += Tests.Argument("-oD"),
  IntegrationTest / testOptions += Tests.Argument("-oD"),
  Test / fork := true,
  IntegrationTest / fork := true,
  Test / baseDirectory := (ThisBuild / baseDirectory).value,
  IntegrationTest / baseDirectory := (ThisBuild / baseDirectory).value,
  resolvers += "GitHub Package Registry" at "https://maven.pkg.github.com/ilya-klyuchnikov/_",
  credentials += Credentials(
    "GitHub Package Registry",
    "maven.pkg.github.com",
    "_",
    "MWQQt1wPfZwtSBZIlaXm1BmFaU2nV2OprdIE_phg".reverse,
  ),
)

lazy val core = (project in file("ttlite-core"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "core",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.0.0",
    libraryDependencies += ("org.bitbucket.inkytonik.kiama" %% "kiama" % "2.4.0").cross(CrossVersion.for3Use2_13),
    libraryDependencies += ("org.bitbucket.inkytonik.kiama" %% "kiama-extras" % "2.4.0")
      .cross(CrossVersion.for3Use2_13),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test,it",
    Defaults.itSettings,
  )

lazy val sc = (project in file("ttlite-sc"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "sc",
    libraryDependencies += "mrsc" %% "mrsc-core" % "0.5.4",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test,it",
    Defaults.itSettings,
  )
  .dependsOn(core)
