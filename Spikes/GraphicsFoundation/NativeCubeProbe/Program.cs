// Copyright 2026 Craig Tiller
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// NONNORMATIVE NATIVE PROBE: this code has no VerifiedProgram or proof authority.

using System.Diagnostics;
using System.Numerics;
using System.Runtime.InteropServices;
using System.Text;
using Veldrid;
using Veldrid.Sdl2;
using Veldrid.SPIRV;
using Veldrid.StartupUtilities;

Console.WriteLine("[probe] NONNORMATIVE: managed Vulkan/Win32 behavior only; no Trust certificate");

double autoCloseSeconds = 0;
for (int i = 0; i + 1 < args.Length; ++i)
{
    if (args[i] == "--auto-close-seconds")
        double.TryParse(args[i + 1], out autoCloseSeconds);
}

WindowCreateInfo windowInfo = new(100, 100, 960, 640, WindowState.Normal, "gasm — unverified Vulkan cube probe");
Sdl2Window window = VeldridStartup.CreateWindow(ref windowInfo);
GraphicsDeviceOptions options = new(
    debug: false,
    swapchainDepthFormat: PixelFormat.D24_UNorm_S8_UInt,
    syncToVerticalBlank: true,
    resourceBindingModel: ResourceBindingModel.Improved,
    preferStandardClipSpaceYDirection: true,
    preferDepthRangeZeroToOne: true);

using GraphicsDevice graphics = VeldridStartup.CreateGraphicsDevice(window, options, GraphicsBackend.Vulkan);
if (graphics.BackendType != GraphicsBackend.Vulkan)
    throw new InvalidOperationException($"Requested Vulkan, received {graphics.BackendType}.");
Console.WriteLine($"[probe] backend={graphics.BackendType}; Escape closes; arrows change spin axis");

ResourceFactory factory = graphics.ResourceFactory;
Vertex[] vertices =
[
    new(-1, -1, -1, 0, 0, 0), new( 1, -1, -1, 1, 0, 0),
    new( 1,  1, -1, 1, 1, 0), new(-1,  1, -1, 0, 1, 0),
    new(-1, -1,  1, 0, 0, 1), new( 1, -1,  1, 1, 0, 1),
    new( 1,  1,  1, 1, 1, 1), new(-1,  1,  1, 0, 1, 1),
];
ushort[] indices =
[
    0, 2, 1, 0, 3, 2, 4, 5, 6, 4, 6, 7,
    0, 1, 5, 0, 5, 4, 2, 3, 7, 2, 7, 6,
    0, 4, 7, 0, 7, 3, 1, 2, 6, 1, 6, 5,
];

using DeviceBuffer vertexBuffer = factory.CreateBuffer(new BufferDescription(
    (uint)(vertices.Length * Marshal.SizeOf<Vertex>()), BufferUsage.VertexBuffer));
using DeviceBuffer indexBuffer = factory.CreateBuffer(new BufferDescription(
    (uint)(indices.Length * sizeof(ushort)), BufferUsage.IndexBuffer));
using DeviceBuffer matrixBuffer = factory.CreateBuffer(new BufferDescription(64, BufferUsage.UniformBuffer | BufferUsage.Dynamic));
graphics.UpdateBuffer(vertexBuffer, 0, vertices);
graphics.UpdateBuffer(indexBuffer, 0, indices);

const string vertexSource = """
    #version 450
    layout(set = 0, binding = 0) uniform Frame { mat4 worldViewProjection; } frame;
    layout(location = 0) in vec3 position;
    layout(location = 1) in vec3 color;
    layout(location = 0) out vec3 vertexColor;
    void main() {
      gl_Position = frame.worldViewProjection * vec4(position, 1.0);
      vertexColor = color;
    }
    """;
const string fragmentSource = """
    #version 450
    layout(location = 0) in vec3 vertexColor;
    layout(location = 0) out vec4 outputColor;
    void main() { outputColor = vec4(vertexColor, 1.0); }
    """;

Shader[] shaders = factory.CreateFromSpirv(
    new ShaderDescription(ShaderStages.Vertex, Encoding.UTF8.GetBytes(vertexSource), "main"),
    new ShaderDescription(ShaderStages.Fragment, Encoding.UTF8.GetBytes(fragmentSource), "main"));
using Shader vertexShader = shaders[0];
using Shader fragmentShader = shaders[1];
using ResourceLayout layout = factory.CreateResourceLayout(new ResourceLayoutDescription(
    new ResourceLayoutElementDescription("Frame", ResourceKind.UniformBuffer, ShaderStages.Vertex)));
using ResourceSet resources = factory.CreateResourceSet(new ResourceSetDescription(layout, matrixBuffer));

VertexLayoutDescription vertexLayout = new(
    new VertexElementDescription("position", VertexElementSemantic.TextureCoordinate, VertexElementFormat.Float3),
    new VertexElementDescription("color", VertexElementSemantic.TextureCoordinate, VertexElementFormat.Float3));
GraphicsPipelineDescription pipelineDescription = new()
{
    BlendState = BlendStateDescription.SingleOverrideBlend,
    DepthStencilState = new DepthStencilStateDescription(true, true, ComparisonKind.LessEqual),
    RasterizerState = new RasterizerStateDescription(
        FaceCullMode.Back, PolygonFillMode.Solid, FrontFace.Clockwise, true, false),
    PrimitiveTopology = PrimitiveTopology.TriangleList,
    ResourceLayouts = [layout],
    ShaderSet = new ShaderSetDescription([vertexLayout], shaders),
    Outputs = graphics.SwapchainFramebuffer.OutputDescription,
};
using Pipeline pipeline = factory.CreateGraphicsPipeline(ref pipelineDescription);
using CommandList commands = factory.CreateCommandList();

window.Resized += () =>
{
    if (window.Width > 0 && window.Height > 0)
        graphics.MainSwapchain.Resize((uint)window.Width, (uint)window.Height);
};

Stopwatch clock = Stopwatch.StartNew();
Vector3 axis = Vector3.Normalize(new Vector3(0.7f, 1.0f, 0.35f));
while (window.Exists)
{
    InputSnapshot input = window.PumpEvents();
    if (!window.Exists) break;
    if (input.IsKeyDown(Key.Escape)) window.Close();
    if (input.IsKeyDown(Key.Left)) axis = Vector3.UnitY;
    if (input.IsKeyDown(Key.Right)) axis = Vector3.UnitX;
    if (input.IsKeyDown(Key.Up)) axis = Vector3.Normalize(new Vector3(1, 1, 0));
    if (autoCloseSeconds > 0 && clock.Elapsed.TotalSeconds >= autoCloseSeconds) window.Close();

    float aspect = Math.Max(1, window.Width) / (float)Math.Max(1, window.Height);
    Matrix4x4 world = Matrix4x4.CreateFromAxisAngle(axis, (float)clock.Elapsed.TotalSeconds);
    Matrix4x4 view = Matrix4x4.CreateLookAt(new Vector3(0, 0, 4.5f), Vector3.Zero, Vector3.UnitY);
    Matrix4x4 projection = Matrix4x4.CreatePerspectiveFieldOfView(1.0f, aspect, 0.1f, 100f);
    Matrix4x4 wvp = Matrix4x4.Transpose(world * view * projection);
    graphics.UpdateBuffer(matrixBuffer, 0, ref wvp);

    commands.Begin();
    commands.SetFramebuffer(graphics.SwapchainFramebuffer);
    commands.ClearColorTarget(0, new RgbaFloat(0.025f, 0.035f, 0.06f, 1f));
    commands.ClearDepthStencil(1f);
    commands.SetPipeline(pipeline);
    commands.SetGraphicsResourceSet(0, resources);
    commands.SetVertexBuffer(0, vertexBuffer);
    commands.SetIndexBuffer(indexBuffer, IndexFormat.UInt16);
    commands.DrawIndexed((uint)indices.Length, 1, 0, 0, 0);
    commands.End();
    graphics.SubmitCommands(commands);
    graphics.SwapBuffers();
}

graphics.WaitForIdle();
Console.WriteLine("[probe] closed after explicit device idle");

[StructLayout(LayoutKind.Sequential)]
readonly struct Vertex
{
    public readonly Vector3 Position;
    public readonly Vector3 Color;
    public Vertex(float x, float y, float z, float r, float g, float b)
    {
        Position = new Vector3(x, y, z);
        Color = new Vector3(r, g, b);
    }
}
