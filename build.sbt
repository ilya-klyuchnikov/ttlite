lazy val commonSettings = Seq(
  scalaVersion := "3.1.0",
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
)

lazy val mrsc = (project in file("mrsc-core"))
  .settings(commonSettings)
  .settings(
    name := "mrsc-core",
  )

lazy val core = (project in file("ttlite-core"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "core",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.0",
    libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.5.0",
    libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama-extras" % "2.5.0",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test,it",
    Defaults.itSettings,
  )

lazy val sc = (project in file("ttlite-sc"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "sc",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test,it",
    Defaults.itSettings,
  )
  .dependsOn(core, mrsc)
