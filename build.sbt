lazy val commonSettings = Seq(
  scalaVersion := "2.12.2",
  organization := "ttlite",
  version := "0.5-SNAPSHOT",
  scalacOptions ++= Seq("-deprecation", "-feature"),
  resolvers += "lambdamix-bintray" at "http://dl.bintray.com/lambdamix/maven/",
  baseDirectory in run := file("."),
  testOptions in Test += Tests.Argument("-oD"),
  testOptions in IntegrationTest += Tests.Argument("-oD"),
  parallelExecution in Test := false,
  parallelExecution in IntegrationTest := false
)

lazy val core = (project in file("ttlite-core"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "core",
    libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.8.0",
    libraryDependencies += "org.fusesource.jansi" %  "jansi" % "1.11",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test,it",
    Defaults.itSettings
  )


lazy val sc = (project in file("ttlite-sc"))
  .configs(IntegrationTest)
  .settings(commonSettings)
  .settings(
    name := "sc",
    libraryDependencies += "mrsc" %% "mrsc-core" % "0.5.2",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test,it",
    Defaults.itSettings
  )
  .dependsOn(core)
