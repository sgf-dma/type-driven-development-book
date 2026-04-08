module Lib

public export
data Shape  = Triangle Double Double
            | Rectangle Double Double
            | Circle Double

triangle : (base : Double) -> (height : Double) -> Shape
triangle = Triangle

rectangle : (width : Double) -> (height : Double) -> Shape
rectangle = Rectangle

circle : (radius : Double) -> Shape
circle = Circle

public export
data ShapeView : Shape -> Type where
  STriangle : {base, height : Double} -> ShapeView (triangle base height)
  SRectangle : {width, height : Double} -> ShapeView (rectangle width height)
  SCircle : {radius : Double} -> ShapeView (circle radius)

export
shapeView : (s : Shape) -> ShapeView s
shapeView (Triangle base height) = STriangle
shapeView (Rectangle width height) = SRectangle
shapeView (Circle radius) = SCircle

area : Shape -> Double
area s with (shapeView s)
  area (triangle base height) | STriangle = 0.5*base*height
  area (rectangle width height) | SRectangle = width*height
  area (circle radius) | SCircle = pi*radius*radius
