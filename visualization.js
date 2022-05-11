const d3 = require('d3')
d3.select(svg).selectAll("*").remove();

function fillPieces(row, col, color, offset) {
  if (color == "red") // Red L-Piece
    d3.select(svg)
      .append("rect")
      .style("fill", "red")
      .attr("x", 5 + (col * 25))
      .attr("y", 5 + (row * 25) + offset * 120)
      .attr('width', 25)
      .attr('height', 25)
  if (color == "blue") // Blue L-Piece
    d3.select(svg)
      .append("rect")
      .style("fill", "blue")
      .attr("x", 5 + (col * 25))
      .attr("y", 5 + (row * 25) + offset * 120)
      .attr('width', 25)
      .attr('height', 25)
  if (color == "neutral") // Neutral
    d3.select(svg)
      .append("rect")
      .style("fill", "purple")
      .attr("x", 5 + (col * 25))
      .attr("y", 5 + (row * 25) + offset * 120)
      .attr('width', 25)
      .attr('height', 25)
}

function printState(inst, offset) {
  drawGrid(offset)
  // Iterate through pieces in Game (red, blue, neutral) and call fillPieces
  const red = inst.field("red").cells.tuples()
  const blue = inst.field("blue").cells.tuples()
  const neutral = inst.field("neutral").tuples()

  for (i = 0; i < 4; i++) {
    var r_row = parseInt((red[i].atoms(0)[1].id())) + 2
    var r_col = parseInt((red[i].atoms(0)[2].id())) + 2
    var b_row = parseInt((blue[i].atoms(0)[1].id())) + 2
    var b_col = parseInt((blue[i].atoms(0)[2].id())) + 2
    fillPieces(r_row, r_col, "red", offset)
    fillPieces(b_row, b_col, "blue", offset)
  }

  for (i = 0; i < 2; i++) {
    var n_row = parseInt(neutral[i].atoms(0)[1].id()) + 2
    var n_col = parseInt(neutral[i].atoms(0)[2].id()) + 2
    fillPieces(n_row, n_col, "neutral", offset)
  }
}

function drawGrid(offset) {
  d3.select(svg)
    .append('rect')
    .attr('x', 5)
    .attr('y', 5 + offset * 120)
    .attr('width', 100)
    .attr('height', 100)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
  for (i = 1; i < 4; i++)
    d3.select(svg)
      .append('line')
      .style("stroke", "black")
      .style("stroke-width", 3)
      .attr("x1", 5)
      .attr("y1", 5 + 25 * i + offset * 120)
      .attr("x2", 105)
      .attr("y2", 5 + 25 * i + offset * 120);
  for (i = 1; i < 4; i++)
    d3.select(svg)
      .append('line')
      .style("stroke", "black")
      .style("stroke-width", 3)
      .attr("x1", 5 + 25 * i)
      .attr("y1", 5 + offset * 120)
      .attr("x2", 5 + 25 * i)
      .attr("y2", 105 + offset * 120);
}

function showLoop() {
  d3.select(svg)
    .append("line")
    .attr("x1", 110)
    .attr("y1", 55 + 120 * (instances.length - 1))
    .attr("x2", 160)
    .attr("y2", 55 + 120 * (instances.length - 1))
    .attr("stroke", "black")
    .attr("stroke-width", 2)

  d3.select(svg)
    .append("line")
    .attr("x1", 160)
    .attr("y1", 55 + 120 * (instances.length - 1))
    .attr("x2", 160)
    .attr("y2", 55 + 120 * loopBack)
    .attr("stroke", "black")
    .attr("stroke-width", 2)

  d3.select(svg)
    .append("line")
    .attr("x1", 160)
    .attr("y1", 55 + 120 * loopBack)
    .attr("x2", 110)
    .attr("y2", 55 + 120 * loopBack)
    .attr("stroke", "black")
    .attr("stroke-width", 2)

  d3.select(svg)
    .append("line")
    .attr("x1", 110)
    .attr("y1", 54 + 120 * loopBack)
    .attr("x2", 115)
    .attr("y2", 60 + 120 * loopBack)
    .attr("stroke", "black")
    .attr("stroke-width", 2)

  d3.select(svg)
    .append("line")
    .attr("x1", 110)
    .attr("y1", 56 + 120 * loopBack)
    .attr("x2", 115)
    .attr("y2", 50 + 120 * loopBack)
    .attr("stroke", "black")
    .attr("stroke-width", 2)
}

instances.map(printState)

if (instances.length - 1 != loopBack) {
  showLoop()
}
