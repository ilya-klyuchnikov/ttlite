githubOwner := "ilya-klyuchnikov"
githubRepository := "ttlite"
githubTokenSource := TokenSource.GitConfig("github.token") || TokenSource.Environment("GITHUB_TOKEN")

lazy val commonSettings = Seq(
  scalaVersion := "2.13.6",
  organization := "ttlite",
  version := "0.5-SNAPSHOT",
  scalacOptions ++= Seq("-deprecation", "-feature"),
  run / baseDirectory := (ThisBuild / baseDirectory).value,
  Test / testOptions += Tests.Argument("-oD"),
  IntegrationTest / testOptions += Tests.Argument("-oD"),
  Test / fork  := true,
  IntegrationTest / fork := true,
  Test / baseDirectory := (ThisBuild / baseDirectory).value,
  IntegrationTest / baseDirectory := (ThisBuild / baseDirectory).value,
  githubOwner := "ilya-klyuchnikov",
  githubRepository := "ttlite",
  githubTokenSource := TokenSource.GitConfig("github.token") || TokenSource.Environment("GITHUB_TOKEN"),
)

lazy val core = (project in file("ttlite-core"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "core",
    libraryDependencies += ("org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2").cross(CrossVersion.for3Use2_13),
    libraryDependencies += ("org.bitbucket.inkytonik.kiama" %% "kiama" % "2.4.0").cross(CrossVersion.for3Use2_13),
    libraryDependencies += ("org.bitbucket.inkytonik.kiama" %% "kiama-extras" % "2.4.0").cross(CrossVersion.for3Use2_13),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test,it",
    Defaults.itSettings,
  )


lazy val sc = (project in file("ttlite-sc"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "sc",
    libraryDependencies += ("mrsc" %% "mrsc-core" % "0.5.3").cross(CrossVersion.for3Use2_13),
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % "test,it",
    Defaults.itSettings,
  )
  .dependsOn(core)
