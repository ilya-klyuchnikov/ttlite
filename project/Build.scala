import sbt._
import Keys._

object SuperSpecBuild extends Build {

  override lazy val settings = super.settings ++ Seq(scalaVersion := "2.10.2")

  lazy val TTProject = Project("tt", file("tt"),
    settings = Project.defaultSettings ++ Seq(
      organization := "mrsc",
      name := "tt",
      version := "0.1",
      libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.5.1",
      libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test",
      baseDirectory in run := file("."),
      testOptions in Test += Tests.Argument("-oD")
    )
  )

  lazy val SuperSpecProject = Project("tt-sc", file("tt-sc"),
    settings = Project.defaultSettings ++ Seq(
      organization := "mrsc",
      name := "tt-sc",
      version := "0.1",
      libraryDependencies += "mrsc" %% "mrsc" % "0.5",
      libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test",
      baseDirectory in run := file(".")
    )
  ) dependsOn(TTProject)

  lazy val root = Project(id = "superspec", base = file(".")) aggregate(TTProject, SuperSpecProject)
}