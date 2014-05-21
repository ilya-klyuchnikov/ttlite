import sbt._
import Keys._

object TTLiteBuild extends Build {

  override lazy val settings = super.settings ++ Seq(
    scalaVersion := "2.11.0",
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

  lazy val CoreProject =
    Project("ttlite-core", file("ttlite-core"))
      .settings( Defaults.itSettings : _*)
      .settings(
        name := "core",
        libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.6.0",
        libraryDependencies += "org.fusesource.jansi" %  "jansi" % "1.11",
        libraryDependencies += "org.scalatest" %% "scalatest" % "2.1.5" % "test,it"
      )
      .configs(IntegrationTest)

  lazy val ScProject =
    Project("ttlite-sc", file("ttlite-sc"))
      .settings( Defaults.itSettings : _*)
      .settings(
        name := "sc",
        libraryDependencies += "mrsc" %% "mrsc" % "0.5.1",
        libraryDependencies += "org.scalatest" %% "scalatest" % "2.1.5" % "test,it"
      )
      .dependsOn(CoreProject)
      .configs(IntegrationTest)

  lazy val root =
    Project(id = "parent", base = file("."))
      .aggregate(CoreProject, ScProject)
}
