lazy val commonSettings = Seq(
  scalaVersion := "2.12.8",
  organization := "ttlite",
  version := "0.5-SNAPSHOT",
  scalacOptions ++= Seq("-deprecation", "-feature"),
  resolvers += "lambdamix-bintray" at "http://dl.bintray.com/lambdamix/maven/",
  run / baseDirectory := file("."),
  Test / testOptions += Tests.Argument("-oD"),
  IntegrationTest / testOptions += Tests.Argument("-oD"),
  Test / fork  := true,
  IntegrationTest / fork := true,
  Test / baseDirectory := file("."),
  IntegrationTest / baseDirectory := file("."),
)

lazy val core = (project in file("ttlite-core"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "core",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2",
    libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.1.0",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test,it",
    Defaults.itSettings,
  )


lazy val sc = (project in file("ttlite-sc"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "sc",
    libraryDependencies += "mrsc" %% "mrsc-core" % "0.5.2",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5" % "test,it",
    Defaults.itSettings,
  )
  .dependsOn(core)
